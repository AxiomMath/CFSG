module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.ONThreePrimePiece
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenPSL

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

attribute [local irreducible] dotProduct

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native.ONTriple Subgroup
open CFSG.GH74.GLS (pPrimeCoreOf)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.ThreePrime
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_row : ∀ j < 2, ∀ l₁ < 4, ∀ l₂ < 4, l₁ < l₂ → ∀ m₁ < 3, ∀ m₂ < 3,
    ∃ k < 9, rowAt j k l₁ = m₁ ∧ rowAt j k l₂ = m₂ := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_nonnormal : ∀ j < 2, ∀ m < 3, ∃ s : Equiv.Perm (Fin 6), Equiv.Perm.sign s = 1 ∧
    s * sV j m 0 * s⁻¹ ≠ 1 ∧ ∀ i < 3, s * sV j m 0 * s⁻¹ ≠ sV j m i := by decide +kernel

section Cores

set_option linter.unusedSectionVars false


@[expose] def core (j : ℕ) (Y : Subgroup GM) (l : ℕ) : Subgroup GM :=
  pPrimeCoreOf 3 (Y ⊓ centralizer ({mL j l} : Set GM))

theorem pPrimeCoreOf_map_conj {G : Type*} [Group G] (p : ℕ) (g : G) (K : Subgroup G) :
    (pPrimeCoreOf p K).map (MulAut.conj g).toMonoidHom =
      pPrimeCoreOf p (K.map (MulAut.conj g).toMonoidHom) := by
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap K
  rw [← CFSG.pPrimeCore_map_iso p ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem core_le (j : ℕ) (Y : Subgroup GM) (l : ℕ) :
    core j Y l ≤ Y ⊓ centralizer ({mL j l} : Set GM) :=
  Subgroup.map_subtype_le _

theorem core_le_left (j : ℕ) (Y : Subgroup GM) (l : ℕ) : core j Y l ≤ Y :=
  (core_le j Y l).trans inf_le_left

theorem not_three_dvd_card_core (j : ℕ) (Y : Subgroup GM) (l : ℕ) :
    ¬ 3 ∣ Nat.card (core j Y l) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := CFSG.pPrimeCore_coprime_card (p := 3)
    (G := ↥(Y ⊓ centralizer ({mL j l} : Set GM)))
  have e : Nat.card (core j Y l) =
      Nat.card (CFSG.pPrimeCore 3 ↥(Y ⊓ centralizer ({mL j l} : Set GM))) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [e]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc

theorem conj_mem_core (j : ℕ) (Y : Subgroup GM) (l : ℕ) {k : GM}
    (hk : k ∈ Y ⊓ centralizer ({mL j l} : Set GM)) {v : GM} (hv : v ∈ core j Y l) :
    k * v * k⁻¹ ∈ core j Y l := by
  obtain ⟨v', hv', rfl⟩ := hv
  refine ⟨(⟨k, hk⟩ : ↥(Y ⊓ centralizer ({mL j l} : Set GM))) * v' * ⟨k, hk⟩⁻¹, ?_, rfl⟩
  exact Subgroup.Normal.conj_mem (inferInstance : (CFSG.pPrimeCore 3 _).Normal) v' hv' ⟨k, hk⟩

theorem AG_le_normalizer_core {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) {Y : Subgroup GM}
    (hY : AG j ≤ normalizer (Y : Set GM)) :
    AG j ≤ normalizer ((core j Y l : Subgroup GM) : Set GM) := by
  intro a ha
  have hcomm : a * mL j l = mL j l * a := AG_comm hj ha (mL_mem_AG hj hl)
  set K := Y ⊓ centralizer ({mL j l} : Set GM) with hKdef
  have hle : K.map (MulAut.conj a).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨(mem_normalizer_iff.1 (hY ha) k).1 hk.1, ?_⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hkm : k * mL j l = mL j l * k := mem_centralizer_singleton_iff.1 hk.2
    show a * k * a⁻¹ * mL j l = mL j l * (a * k * a⁻¹)
    calc a * k * a⁻¹ * mL j l = a * k * (a⁻¹ * mL j l * a) * a⁻¹ := by group
      _ = a * k * mL j l * a⁻¹ := by
        have : a⁻¹ * mL j l * a = mL j l := by
          calc a⁻¹ * mL j l * a = a⁻¹ * (mL j l * a) := by group
            _ = a⁻¹ * (a * mL j l) := by rw [hcomm]
            _ = mL j l := by group
        rw [this]
      _ = a * (k * mL j l) * a⁻¹ := by group
      _ = a * (mL j l * k) * a⁻¹ := by rw [hkm]
      _ = mL j l * (a * k * a⁻¹) := by
        calc a * (mL j l * k) * a⁻¹ = (a * mL j l) * k * a⁻¹ := by group
          _ = (mL j l * a) * k * a⁻¹ := by rw [hcomm]
          _ = mL j l * (a * k * a⁻¹) := by group
  have hK : K.map (MulAut.conj a).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm)
  have hV : (core j Y l).map (MulAut.conj a).toMonoidHom = core j Y l := by
    rw [core, pPrimeCoreOf_map_conj, ← hKdef, hK]
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : a * h * a⁻¹ ∈ (core j Y l).map (MulAut.conj a).toMonoidHom := ⟨h, hh, by simp⟩
    rwa [hV] at this
  · intro hh
    have ha' : a⁻¹ ∈ AG j := inv_mem ha
    have hcomm' : a⁻¹ * mL j l = mL j l * a⁻¹ := by
      calc a⁻¹ * mL j l = a⁻¹ * (mL j l * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * mL j l) * a⁻¹ := by rw [hcomm]
        _ = mL j l * a⁻¹ := by group
    have hle' : K.map (MulAut.conj a⁻¹).toMonoidHom ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨(mem_normalizer_iff.1 (hY ha') k).1 hk.1, ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have hkm : k * mL j l = mL j l * k := mem_centralizer_singleton_iff.1 hk.2
      show a⁻¹ * k * a⁻¹⁻¹ * mL j l = mL j l * (a⁻¹ * k * a⁻¹⁻¹)
      calc a⁻¹ * k * a⁻¹⁻¹ * mL j l = a⁻¹ * k * (a * mL j l * a⁻¹) * a := by group
        _ = a⁻¹ * k * mL j l * a := by
          have : a * mL j l * a⁻¹ = mL j l := by
            calc a * mL j l * a⁻¹ = (a * mL j l) * a⁻¹ := by group
              _ = (mL j l * a) * a⁻¹ := by rw [hcomm]
              _ = mL j l := by group
          rw [this]
        _ = a⁻¹ * (k * mL j l) * a := by group
        _ = a⁻¹ * (mL j l * k) * a := by rw [hkm]
        _ = mL j l * (a⁻¹ * k * a⁻¹⁻¹) := by
          calc a⁻¹ * (mL j l * k) * a = (a⁻¹ * mL j l) * k * a := by group
            _ = (mL j l * a⁻¹) * k * a := by rw [hcomm']
            _ = mL j l * (a⁻¹ * k * a⁻¹⁻¹) := by group
    have hK' : K.map (MulAut.conj a⁻¹).toMonoidHom = K :=
      Subgroup.eq_of_le_of_card_ge hle'
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective).symm)
    have hV' : (core j Y l).map (MulAut.conj a⁻¹).toMonoidHom = core j Y l := by
      rw [core, pPrimeCoreOf_map_conj, ← hKdef, hK']
    have : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ ∈ (core j Y l).map (MulAut.conj a⁻¹).toMonoidHom :=
      ⟨a * h * a⁻¹, hh, by simp⟩
    rw [hV'] at this
    simpa [mul_assoc] using this

theorem core_cases {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) {Y : Subgroup GM}
    (hY : AG j ≤ normalizer (Y : Set GM)) :
    core j Y l = ⊥ ∨ ∃ (m : ℕ) (hm : m < 3), core j Y l = XG j l m hj hm := by
  have h := piece_threePrime hj hl (core j Y l) (not_three_dvd_card_core j Y l)
    (AG_le_normalizer_core hj hl hY)
  rwa [inf_eq_left.2 ((core_le j Y l).trans inf_le_right)] at h

theorem xE_mem_XG {j l m : ℕ} (hj : j < 2) (hm : m < 3) (i : ℕ) (hi : i < 3) :
    xE j l m i ∈ XG j l m hj hm := by
  rw [mem_XG]
  have : nL j l * xE j l m i * (nL j l)⁻¹ = vG j m i := by
    unfold xE; group
  rw [this, mem_VG]
  exact Or.inr ⟨i, hi, rfl⟩

theorem xE_ne_one {j l m : ℕ} (hj : j < 2) (hm : m < 3) {i : ℕ} (hi : i < 3) :
    xE j l m i ≠ 1 := by
  intro h
  have h2 : vG j m i = 1 := by
    have : vG j m i = nL j l * xE j l m i * (nL j l)⁻¹ := by unfold xE; group
    rw [this, h]; group
  exact (chkV_facts hj hm).2.2.1 i hi |>.2 h2

theorem XG_eq_closure {j l m : ℕ} (hj : j < 2) (hm : m < 3) :
    XG j l m hj hm = Subgroup.closure ({xE j l m 0, xE j l m 1} : Set GM) := by
  apply le_antisymm
  · intro g hg
    rw [mem_XG, mem_VG] at hg
    rcases hg with h | ⟨i, hi, h⟩
    · have : g = 1 := by
        have h' : g = (nL j l)⁻¹ * (nL j l * g * (nL j l)⁻¹) * nL j l := by group
        rw [h', h]; group
      rw [this]; exact one_mem _
    · have hg' : g = (nL j l)⁻¹ * (nL j l * g * (nL j l)⁻¹) * nL j l := by group
      rw [hg', h]
      interval_cases i
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr rfl)
      · have h01 := (chkV_facts hj hm).1
        have : (nL j l)⁻¹ * vG j m 2 * nL j l = xE j l m 0 * xE j l m 1 := by
          rw [← h01]; unfold xE; group
        rw [this]
        exact mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact xE_mem_XG hj hm 0 (by norm_num)
    · exact xE_mem_XG hj hm 1 (by norm_num)

theorem VG_not_normal {j m : ℕ} (hj : j < 2) (hm : m < 3) :
    ∃ g : K0G, (g : GM) * vG j m 0 * (g : GM)⁻¹ ∉ VG j m hj hm := by
  obtain ⟨s, hs, hs1, hs2⟩ := exists_nonnormal j hj m hm
  have hsA : s ∈ (actK : K0G →* Equiv.Perm (Fin 6)).range := by
    rw [range_actK]; exact Equiv.Perm.mem_alternatingGroup.2 hs
  obtain ⟨g, hg⟩ := hsA
  refine ⟨g, fun hx => ?_⟩
  set ve : K0G := ⟨vG j m 0, vG_mem_K0 hj hm (by norm_num)⟩ with hve
  have hact : actK (g * ve * g⁻¹) = s * sV j m 0 * s⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg, hve, actK_vG hj hm (by norm_num)]
  rcases (mem_VG.1 hx) with h | ⟨i, hi, h⟩
  · apply hs1
    rw [← hact]
    have : g * ve * g⁻¹ = 1 := Subtype.ext (show (g : GM) * vG j m 0 * (g : GM)⁻¹ = 1 from h)
    rw [this, map_one]
  · apply hs2 i hi
    rw [← hact]
    have : g * ve * g⁻¹ = ⟨vG j m i, vG_mem_K0 hj hm hi⟩ :=
      Subtype.ext (show (g : GM) * vG j m 0 * (g : GM)⁻¹ = vG j m i from h)
    rw [this, actK_vG hj hm hi]

theorem core_top_eq_bot {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    core j ⊤ l = ⊥ := by
  rcases core_cases hj hl (Y := ⊤) (fun a _ => mem_normalizer_iff.2 fun h => by simp) with
    h | ⟨m, hm, h⟩
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := VG_not_normal hj hm
    have hk : (nL j l)⁻¹ * (g : GM) * nL j l ∈ (⊤ : Subgroup GM) ⊓ centralizer ({mL j l} : Set GM) := by
      refine ⟨trivial, ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have hc : (g : GM) * xG 0 = xG 0 * (g : GM) := K0_comm g.2
      have e : mL j l = (nL j l)⁻¹ * xG 0 * nL j l := rfl
      rw [e]
      calc (nL j l)⁻¹ * (g : GM) * nL j l * ((nL j l)⁻¹ * xG 0 * nL j l) = (nL j l)⁻¹ * ((g : GM) * xG 0) * nL j l := by group
        _ = (nL j l)⁻¹ * (xG 0 * (g : GM)) * nL j l := by rw [hc]
        _ = (nL j l)⁻¹ * xG 0 * nL j l * ((nL j l)⁻¹ * (g : GM) * nL j l) := by group
    have hv : xE j l m 0 ∈ core j ⊤ l := by rw [h]; exact xE_mem_XG hj hm 0 (by norm_num)
    have := conj_mem_core j ⊤ l hk hv
    rw [h, mem_XG] at this
    apply hg
    have e : nL j l * ((nL j l)⁻¹ * (g : GM) * nL j l * xE j l m 0 * ((nL j l)⁻¹ * (g : GM) * nL j l)⁻¹) * (nL j l)⁻¹ =
        (g : GM) * vG j m 0 * (g : GM)⁻¹ := by unfold xE; group
    rwa [← e]

theorem xE_mem_Lk {j k : ℕ} (hj : j < 2) (hk : k < 9) {l i : ℕ}
    (hl : l < 4) (hi : i < 2) :
    xE j l (rowAt j k l) i ∈ Subgroup.closure (Set.range (lY j k)) := by
  interval_cases l <;> interval_cases i
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩
  · simpa using mem_closure_in hj hk 0 (by norm_num)
  · simpa using mem_closure_in hj hk 1 (by norm_num)
  · simpa using mem_closure_in hj hk 2 (by norm_num)
  · simpa using mem_closure_in hj hk 3 (by norm_num)

theorem XG_le_Lk {j k : ℕ} (hj : j < 2) (hk : k < 9) {l : ℕ}
    (hl : l < 4) :
    XG j l (rowAt j k l) hj (rowAt_lt j hj k hk l hl) ≤ Subgroup.closure (Set.range (lY j k)) := by
  rw [XG_eq_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact xE_mem_Lk hj hk hl (by norm_num)
  · exact xE_mem_Lk hj hk hl (by norm_num)

theorem tuple_eq_L37
    {j : ℕ} (hj : j < 2) {Y : Subgroup GM} (hY : AG j ≤ normalizer (Y : Set GM))
    {l₁ l₂ : ℕ} (hl : l₁ < l₂) (h₂ : l₂ < 4) (hv₁ : core j Y l₁ ≠ ⊥) (hv₂ : core j Y l₂ ≠ ⊥) :
    (∃ k < 9, (⨆ ℓ : Fin 4, core j Y ℓ) = Subgroup.closure (Set.range (lY j k))) ∧
    Nat.card ↥(⨆ ℓ : Fin 4, core j Y ℓ) = 1876896 ∧
      ∃ _ : Fact (Nat.Prime 7), Nonempty (↥(⨆ ℓ : Fin 4, core j Y ℓ) ⧸
        aschbacherSolvableCore 3 ↥(⨆ ℓ : Fin 4, core j Y ℓ) ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) := by
  have h₁ : l₁ < 4 := hl.trans h₂
  set T : Subgroup GM := ⨆ ℓ : Fin 4, core j Y ℓ with hT
  have hTY : T ≤ Y := iSup_le fun ℓ => core_le_left j Y ℓ
  obtain ⟨m₁, hm₁, e₁⟩ := (core_cases hj h₁ hY).resolve_left hv₁
  obtain ⟨m₂, hm₂, e₂⟩ := (core_cases hj h₂ hY).resolve_left hv₂
  obtain ⟨k, hk, hr₁, hr₂⟩ := exists_row j hj l₁ h₁ l₂ h₂ hl m₁ hm₁ m₂ hm₂
  set Lk := Subgroup.closure (Set.range (lY j k)) with hLk
  have hrow0 := rowAt_lt j hj k hk 0 (by norm_num)
  have hLk_ne : Lk ≠ ⊥ := by
    intro h
    have hx : xE j 0 (rowAt j k 0) 0 ∈ Lk :=
      xE_mem_Lk (j := j) (k := k) hj hk (l := 0) (i := 0) (by norm_num) (by norm_num)
    rw [h, Subgroup.mem_bot] at hx
    exact xE_ne_one hj hrow0 (i := 0) (by norm_num) hx
  obtain ⟨yk, hyk, hclk⟩ := exists_rels_lY hj hk
  have hLk_card : Nat.card Lk = 1876896 := card_closure_eq yk hyk hclk hLk_ne
  set Lp := Subgroup.closure (Set.range (pairY j l₁ m₁ l₂ m₂)) with hLp
  have hLp_ne : Lp ≠ ⊥ := by
    intro h
    have hx : xE j l₁ m₁ 0 ∈ Lp := Subgroup.subset_closure ⟨0, rfl⟩
    rw [h, Subgroup.mem_bot] at hx
    exact xE_ne_one hj hm₁ (i := 0) (by norm_num) hx
  obtain ⟨yp, hyp, hclp⟩ := exists_rels_pair hj h₁ h₂ hl m₁ m₂ hm₁ hm₂
  have hLp_card : Nat.card Lp = 1876896 := card_closure_eq yp hyp hclp hLp_ne
  have hLpLk : Lp ≤ Lk := by
    rw [hLp, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    fin_cases x
    · have := xE_mem_Lk hj hk (l := l₁) (i := 0) h₁ (by norm_num)
      rwa [hr₁] at this
    · have := xE_mem_Lk hj hk (l := l₁) (i := 1) h₁ (by norm_num)
      rwa [hr₁] at this
    · have := xE_mem_Lk hj hk (l := l₂) (i := 0) h₂ (by norm_num)
      rwa [hr₂] at this
    · have := xE_mem_Lk hj hk (l := l₂) (i := 1) h₂ (by norm_num)
      rwa [hr₂] at this
  have hLpT : Lp ≤ T := by
    rw [hLp, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    fin_cases x
    · have : xE j l₁ m₁ 0 ∈ core j Y l₁ := by rw [e₁]; exact xE_mem_XG hj hm₁ 0 (by norm_num)
      exact le_iSup (fun ℓ : Fin 4 => core j Y ℓ) ⟨l₁, h₁⟩ this
    · have : xE j l₁ m₁ 1 ∈ core j Y l₁ := by rw [e₁]; exact xE_mem_XG hj hm₁ 1 (by norm_num)
      exact le_iSup (fun ℓ : Fin 4 => core j Y ℓ) ⟨l₁, h₁⟩ this
    · have : xE j l₂ m₂ 0 ∈ core j Y l₂ := by rw [e₂]; exact xE_mem_XG hj hm₂ 0 (by norm_num)
      exact le_iSup (fun ℓ : Fin 4 => core j Y ℓ) ⟨l₂, h₂⟩ this
    · have : xE j l₂ m₂ 1 ∈ core j Y l₂ := by rw [e₂]; exact xE_mem_XG hj hm₂ 1 (by norm_num)
      exact le_iSup (fun ℓ : Fin 4 => core j Y ℓ) ⟨l₂, h₂⟩ this
  have hLpeq : Lp = Lk := Subgroup.eq_of_le_of_card_ge hLpLk (by rw [hLk_card, hLp_card])
  have hLkT : Lk ≤ T := hLpeq ▸ hLpT
  have hcase : (∀ ℓ : Fin 4, core j Y ℓ ≤ Lk) ∨ T = ⊤ := by
    by_cases hall : ∀ ℓ : Fin 4, core j Y ℓ ≤ Lk
    · exact Or.inl hall
    · right
      push Not at hall
      obtain ⟨ℓ, hℓ⟩ := hall
      rcases core_cases hj ℓ.2 hY with h | ⟨m, hm, hmX⟩
      · exact absurd (h ▸ bot_le) hℓ
      · have hmrow : m ≠ rowAt j k ℓ := by
          intro hm'
          apply hℓ
          subst hm'
          rw [hmX]
          exact XG_le_Lk hj hk ℓ.2
        have htop := closure_top hj hk ℓ.2 hm hmrow
        rw [eq_top_iff, ← htop, Subgroup.closure_le]
        rintro x (⟨y, rfl⟩ | hx)
        · exact hLkT (Subgroup.subset_closure ⟨y, rfl⟩)
        · have hmem : ∀ i < 3, xE j ℓ m i ∈ T := fun i hi =>
            le_iSup (fun ℓ : Fin 4 => core j Y ℓ) ℓ (by rw [hmX]; exact xE_mem_XG hj hm i hi)
          rcases hx with rfl | rfl
          · exact hmem 0 (by norm_num)
          · exact hmem 1 (by norm_num)
  rcases hcase with hall | htop
  · have hTLk : T ≤ Lk := iSup_le hall
    have hTeq : T = Lk := le_antisymm hTLk hLkT
    have hcard : Nat.card T = 1876896 := by rw [hTeq]; exact hLk_card
    refine ⟨⟨k, hk, hTeq⟩, hcard, ?_⟩
    exact quot_projSL yk hyk (hclk.trans hTeq.symm) (by rw [hTeq]; exact hLk_ne)
  · exfalso
    have hY' : Y = ⊤ := eq_top_iff.2 (htop ▸ hTY)
    rw [hY', core_top_eq_bot hj h₁] at hv₁
    exact hv₁ rfl

theorem tuple_L37
    {j : ℕ} (hj : j < 2) {Y : Subgroup GM} (hY : AG j ≤ normalizer (Y : Set GM))
    {l₁ l₂ : ℕ} (hl : l₁ < l₂) (h₂ : l₂ < 4) (hv₁ : core j Y l₁ ≠ ⊥) (hv₂ : core j Y l₂ ≠ ⊥) :
    Nat.card ↥(⨆ ℓ : Fin 4, core j Y ℓ) = 1876896 ∧
      ∃ _ : Fact (Nat.Prime 7), Nonempty (↥(⨆ ℓ : Fin 4, core j Y ℓ) ⧸
        aschbacherSolvableCore 3 ↥(⨆ ℓ : Fin 4, core j Y ℓ) ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
  (tuple_eq_L37 hj hY hl h₂ hv₁ hv₂).2

end Cores

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
