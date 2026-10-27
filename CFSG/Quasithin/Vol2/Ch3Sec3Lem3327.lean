module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3326
public import CFSG.GroupTheory.Frattini.MapSubtypeLe
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

@[expose] def FactL32CentralInv : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (A K S : Subgroup Ω), K ≤ A →
    A ≤ Subgroup.normalizer (K : Set Ω) → IsPSL 3 2 1 ↥K → (∀ a ∈ A, ∃ e : ℕ, a ^ 2 ^ e ∈ K) →
    pCoreOf 2 A = ⊥ → IsSylowTwoOf S A →
    ∀ z₁ ∈ S, ∀ z₂ ∈ S, (∀ s ∈ S, z₁ * s = s * z₁) → (∀ s ∈ S, z₂ * s = s * z₂) →
      z₁ ^ 2 = 1 → z₂ ^ 2 = 1 → z₁ ≠ 1 → z₂ ≠ 1 → z₁ = z₂

@[expose] def Insp3_3_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → (IsAltBlockType L 6 ∨ IsG2Block L ∨ IsLnBlock L 3) →
    ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
    ∀ z₁ ∈ autOn T (vPlus L T), ∀ z₂ ∈ autOn T (vPlus L T),
      (∀ s ∈ autOn T (vPlus L T), z₁ * s = s * z₁) →
      (∀ s ∈ autOn T (vPlus L T), z₂ * s = s * z₂) → z₁ ^ 2 = 1 → z₂ ^ 2 = 1 → z₁ ≠ 1 →
      z₂ ≠ 1 →
      (∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
          (vPlus L T), z₁ * y = y * z₁) →
      (∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
          (vPlus L T), z₂ * y = y * z₂) → z₁ = z₂

namespace Ch3Sec3

section Generic

variable {Ω : Type} [Group Ω]

theorem exists_central_involution [Finite Ω] {S N : Subgroup Ω} (hS : IsPGroup 2 ↥S)
    (hNS : N ≤ S) (hSN : S ≤ Subgroup.normalizer (N : Set Ω)) (hN : N ≠ ⊥) :
    ∃ z ∈ N, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ s ∈ S, z * s = s * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have : (N.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSN
  have hne : N.subgroupOf S ≠ ⊥ := by
    intro hb
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNS, hb, Subgroup.map_bot]
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨k, hk⟩ := (hS.to_subgroup (N.subgroupOf S ⊓ Subgroup.center ↥S)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hW (Subgroup.eq_bot_of_card_eq _ hk)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hw2 : w ^ 2 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have hw1 : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw
    exact absurd hw (by norm_num)
  refine ⟨((w : ↥S) : Ω), Subgroup.mem_subgroupOf.mp w.2.1, fun h => hw1 ?_, ?_, ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have h2 := congrArg (fun x : ↥(N.subgroupOf S ⊓ Subgroup.center ↥S) => ((x : ↥S) : Ω)) hw2
    simpa using h2
  · intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2.2 ⟨s, hs⟩).symm

theorem map_frattini_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (ι : P ≃* Q) :
    (frattini P).map ι.toMonoidHom = frattini Q := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective ι.surjective
  · have h := frattini_le_comap_frattini_of_surjective (φ := ι.symm.toMonoidHom) ι.symm.surjective
    exact ⟨ι.symm x, h hx, by simp⟩

theorem frattini_map_le_of_sq [Finite Ω] {A K : Subgroup Ω} (hA : IsPGroup 2 ↥A)
    (hK : ∀ a ∈ A, a ^ 2 ∈ K) : (frattini ↥A).map A.subtype ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥A) := ⟨hA⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hx | ⟨y, rfl⟩
  · have hle : commutator ↥A ≤ K.comap A.subtype := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap]
      have e : A.subtype ⁅a, b⁆ = (a : Ω) ^ 2 * ((a : Ω)⁻¹ * b) ^ 2 * ((b : Ω)⁻¹) ^ 2 := by
        simp only [Subgroup.coe_subtype, commutatorElement_def, Subgroup.coe_mul,
          Subgroup.coe_inv, pow_two]
        group
      rw [e]
      exact K.mul_mem (K.mul_mem (hK _ a.2) (hK _ (A.mul_mem (A.inv_mem a.2) b.2)))
        (hK _ (A.inv_mem b.2))
    exact hle hx
  · simpa using hK _ y.2

theorem frattini_map_mono [Finite Ω] {A B : Subgroup Ω} (hB : IsPGroup 2 ↥B) (hAB : A ≤ B) :
    (frattini ↥A).map A.subtype ≤ (frattini ↥B).map B.subtype :=
  CFSG.GroupTheory.frattini_map_subtype_mono hB hAB

theorem frattini_map_conj_eq_bot_iff {A : Subgroup Ω} (g : Ω) :
    frattini ↥(A.map (MulAut.conj g).toMonoidHom) = ⊥ ↔ frattini ↥A = ⊥ := by
  rw [← map_frattini_of_mulEquiv (A.equivMapOfInjective _ (MulAut.conj g).injective),
    Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)]

theorem le_normalizer_map_conj {T Y : Subgroup Ω} {g : Ω}
    (hg : g ∈ Subgroup.normalizer (T : Set Ω)) (hTY : T ≤ Subgroup.normalizer (Y : Set Ω)) :
    T ≤ Subgroup.normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup Ω) : Set Ω) := by
  refine le_normalizer_of_conj_le fun t ht x hx => ?_
  rw [A38.mem_map_conj] at hx ⊢
  have ht' : g⁻¹ * t * g ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t).mp ht
    simpa using this
  have := (Subgroup.mem_normalizer_iff.mp (hTY ht') _).mp hx
  have e : g⁻¹ * (t * x * t⁻¹) * g = g⁻¹ * t * g * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by group
  rw [e]
  exact this

end Generic

end Ch3Sec3

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem isTwoLocal_map_conj' {K : Subgroup G} (hK : IsTwoLocal K) (g : G) :
    IsTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
  · intro hb
    exact hP ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).mp hb)
  · exact Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective

omit [Finite G] in
theorem map_conj_map_conj_inv' (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  ext x
  rw [A38.mem_map_conj, A38.mem_map_conj]
  simp [mul_assoc]

omit [Finite G] in
theorem quasithinIsMaxTwoLocal_map_conj' {K : Subgroup G} (hK : quasithinIsMaxTwoLocal K)
    (g : G) : quasithinIsMaxTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isTwoLocal_map_conj' hK.1 g, fun H hH hKH => ?_⟩
  have hH' := isTwoLocal_map_conj' hH g⁻¹
  have hKH' : K ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hKH
    rwa [map_conj_map_conj_inv'] at this
  have h1 := hK.2 _ hH' hKH'
  have h3 := map_conj_map_conj_inv' H g⁻¹
  rw [inv_inv] at h3
  rw [← h3, h1]

theorem normalizer_le_of_isMaxTwoLocal {M : Subgroup G} (hM : quasithinIsMaxTwoLocal M) :
    Subgroup.normalizer (M : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  have hPO : P ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMP ▸ Subgroup.le_normalizer)
      (le_of_eq hMP) hP2
  have hO : pCoreOf 2 M ≠ ⊥ := fun hb => hP (le_bot_iff.mp (hb ▸ hPO))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have heq := hM.2 _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M).trans heq.le

omit [Finite G] in
theorem mem_zpowers_sq_of_odd {d : G} (hd : Odd (orderOf d)) :
    d ∈ Subgroup.zpowers (d ^ 2) := by
  obtain ⟨k, hk⟩ := hd
  refine ⟨((k + 1 : ℕ) : ℤ), ?_⟩
  simp only [zpow_natCast, ← pow_mul]
  calc d ^ (2 * (k + 1)) = d ^ (2 * k + 1) * d := by rw [← pow_succ]; congr 1
    _ = d := by rw [← hk, pow_orderOf_eq_one, one_mul]

namespace Hyp331

theorem sq_not_mem (h : Hyp331 G T M L D) {d : G} (hdD : d ∈ D) (hdM : d ∉ M) :
    d ^ 2 ∉ M := by
  intro hsq
  apply hdM
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  exact (Subgroup.zpowers_le.mpr hsq) (mem_zpowers_sq_of_odd hodd)

omit [Finite G] in
theorem le_normalizer_tC (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (tC L T : Set G) := fun _ ht =>
  mem_normalizer_inf (Subgroup.le_normalizer ht)
    (B2F.normalizer_le_normalizer_centralizer L (hTL ht))

theorem tC_inf_conjugate_eq_bot
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) : tC L T ⊓ CFSG.conjugate (tC L T) d = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hTTC := le_normalizer_tC hTL
  set X := tC L T ⊓ CFSG.conjugate (tC L T) d with hXdef
  have hXT : X ≤ T := inf_le_left.trans inf_le_left
  have hX2 : IsPGroup 2 ↥X := h.sylow.1.to_le hXT
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    mem_normalizer_inf (hTTC ht) (le_normalizer_map_conj (inv_mem hdT) hTTC ht)
  have hLC : ∀ Y : Subgroup G, Y ≤ tC L T → L ≤ Subgroup.normalizer (Y : Set G) := by
    intro Y hY
    refine le_normalizer_of_conj_le fun l hl y hy => ?_
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hY hy)).2 l hl
    rw [hc, mul_inv_cancel_right]
    exact hy
  have hLTX : L ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le (hLC X inf_le_left) hTX
  have hNX : Subgroup.normalizer (X : Set G) ≤ M :=
    h.toSetup331.normalizer_le h38 h39 hne hX2 hLTX
  set X' := X.map (MulAut.conj d).toMonoidHom with hX'def
  have hX'C : X' ≤ tC L T := by
    intro x hx
    rw [A38.mem_map_conj] at hx
    have hx2 := (Subgroup.mem_inf.mp hx).2
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv] at hx2
    simpa [mul_assoc] using hx2
  have hX'ne : X' ≠ ⊥ := by
    rw [hX'def, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj d).injective]
    exact hne
  have hX'2 : IsPGroup 2 ↥X' := hX2.map _
  have hNX' : Subgroup.normalizer (X' : Set G) ≤ M :=
    h.toSetup331.normalizer_le h38 h39 hX'ne hX'2
      (sup_le (hLC X' hX'C) (le_normalizer_map_conj hdT hTX))
  have hNXM : Subgroup.normalizer (X : Set G) ≤ M.map (MulAut.conj d⁻¹).toMonoidHom := by
    intro n hn
    rw [A38.mem_map_conj, inv_inv]
    refine hNX' ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [A38.mem_map_conj, A38.mem_map_conj]
    have e : d⁻¹ * (d * n * d⁻¹ * y * (d * n * d⁻¹)⁻¹) * d = n * (d⁻¹ * y * d) * n⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hn _
  have hmax := quasithinIsMaxTwoLocal_map_conj' h.maxM d⁻¹
  have hMeq : M.map (MulAut.conj d⁻¹).toMonoidHom = M :=
    (h.toSetup331.isUniqueM h38 h39).2 _ ⟨hmax, fun x hx => hNXM (hLTX hx)⟩
  have hdinv : d⁻¹ ∈ M := normalizer_le_of_isMaxTwoLocal h.maxM (A38.map_conj_eq_iff.mp hMeq)
  exact hdM (by simpa using M.inv_mem hdinv)

theorem frattini_qL_le_tC
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hshort : IsShort2 L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    (frattini ↥(qL L T)).map (qL L T).subtype ≤ tC L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := vPlus_reduced h.toSetup331
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hUV := h.blockU_le_vPlus h38 h39 hshort hTL
  have hQU := commutator_qL_le_blockU hshort hTL
  refine frattini_map_le_of_sq hQ2 fun q hq =>
    Subgroup.mem_inf.mpr ⟨T.pow_mem (hQT hq) 2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hw : q * l * q⁻¹ * l⁻¹ ∈ vPlus L T := by
    have := hUV (hQU (Subgroup.commutator_mem_commutator hq hl))
    simpa [commutatorElement_def] using this
  set w := q * l * q⁻¹ * l⁻¹ with hwdef
  have hwq : q * w = w * q :=
    Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hw) q hq
  have hw2 : w * w = 1 := by
    have := hred.2.1.2 w hw
    rwa [pow_two] at this
  have hwl : q * l * q⁻¹ = w * l := by rw [hwdef]; group
  have key : q ^ 2 * l = l * q ^ 2 := by
    calc q ^ 2 * l = q * (q * l * q⁻¹) * q := by rw [pow_two]; group
      _ = q * (w * l) * q := by rw [hwl]
      _ = (q * w) * l * q := by group
      _ = (w * q) * l * q := by rw [hwq]
      _ = w * (q * l * q⁻¹) * q * q := by group
      _ = w * (w * l) * q * q := by rw [hwl]
      _ = (w * w) * l * q * q := by group
      _ = l * q ^ 2 := by rw [hw2, pow_two]; group
  exact key.symm

theorem tC_le_qL
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : tC L T ≤ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMp := mPlus_eq_of_le hTL
  have hred := vPlus_reduced h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) (vPlus L T)) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  obtain ⟨-, hXK, h2X, -⟩ := h.autOn_data
  rw [hMp] at hXK h2X
  intro t ht
  have htV : t ∈ Subgroup.normalizer (vPlus L T : Set G) := hHV (Subgroup.mem_sup_right ht.1)
  have hx : conjAct (vPlus L T) ⟨t, htV⟩ ∈ autOn (L ⊔ T) (vPlus L T) :=
    CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨t, htV⟩, Subgroup.mem_sup_right ht.1, rfl⟩
  have hc : ∀ k ∈ autOn L (vPlus L T),
      k * conjAct (vPlus L T) ⟨t, htV⟩ = conjAct (vPlus L T) ⟨t, htV⟩ * k := by
    intro k hk
    obtain ⟨g, hg, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hk
    rw [← map_mul, ← map_mul,
      show g * ⟨t, htV⟩ = ⟨t, htV⟩ * g from Subtype.ext (Subgroup.mem_centralizer_iff.mp ht.2 g hg)]
  obtain ⟨e, he⟩ := h.sylow.1 ⟨t, ht.1⟩
  have hxe : conjAct (vPlus L T) ⟨t, htV⟩ ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have h1 : (⟨t, htV⟩ : Subgroup.normalizer (vPlus L T : Set G)) ^ 2 ^ e = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val he
      simpa using this
    rw [h1, map_one]
  have h1 := eq_one_of_two_of_commute hXK h2X hO2 hx hc hxe
  have htC : t ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := congrArg (fun φ : MulAut ↥(vPlus L T) => ((φ ⟨v, hv⟩ : ↥(vPlus L T)) : G)) h1
    simp only [InternalSec.coe_conjAct_apply, MulAut.one_apply] at this
    calc v * t = (t * v * t⁻¹) * t := by rw [this]
      _ = t * v := by group
  show t ∈ pCoreOf 2 (L ⊔ T)
  rw [← (h.centralizer_vPlus h38 h39).2.1]
  exact ⟨ht.1, htC⟩

omit [Finite G] in
theorem map_conj_le_of_le {X : Subgroup G} (hXT : X ≤ T) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : X.map (MulAut.conj g).toMonoidHom ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hXT hx)

theorem three_of_uniq
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdD : d ∈ D) (hdM : d ∉ M)
    {Y : Subgroup G}
    (hY₁ : ∀ x ∈ CFSG.conjugate (tC L T) d, ∀ y ∈ Y, x * y = y * x)
    (hY₂ : ∀ x ∈ CFSG.conjugate (tC L T) d⁻¹, ∀ y ∈ Y, x * y = y * x)
    (huniq : ∀ z₁ ∈ autOn T (vPlus L T), ∀ z₂ ∈ autOn T (vPlus L T),
      (∀ s ∈ autOn T (vPlus L T), z₁ * s = s * z₁) →
      (∀ s ∈ autOn T (vPlus L T), z₂ * s = s * z₂) → z₁ ^ 2 = 1 → z₂ ^ 2 = 1 → z₁ ≠ 1 →
      z₂ ≠ 1 → (∀ y ∈ autOn Y (vPlus L T), z₁ * y = y * z₁) →
      (∀ y ∈ autOn Y (vPlus L T), z₂ * y = y * z₂) → z₁ = z₂) :
    CFSG.conjugate (tC L T) d ≤ qL L T ∨ tC L T ≤ CFSG.conjugate (qL L T) d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hTTC := le_normalizer_tC hTL
  have hred := vPlus_reduced h.toSetup331
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hCQ := (h.centralizer_vPlus h38 h39).2.1
  have h₂' : ¬ CFSG.conjugate (tC L T) d⁻¹ ≤ qL L T := by
    intro hle
    apply h₂
    intro x hx
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv]
    refine hle ?_
    rw [CFSG.conjugate, A38.mem_map_conj]
    simpa [mul_assoc] using hx
  have hS2 : IsPGroup 2 ↥(autOn T (vPlus L T)) := Lem328.isPGroup_autOn h.sylow.1
  have key : ∀ g : G, g ∈ Subgroup.normalizer (T : Set G) →
      ¬ (tC L T).map (MulAut.conj g).toMonoidHom ≤ qL L T →
      ∃ n ∈ (tC L T).map (MulAut.conj g).toMonoidHom, ∃ hn : n ∈ Subgroup.normalizer
        (vPlus L T : Set G), conjAct (vPlus L T) ⟨n, hn⟩ ≠ 1 ∧
        conjAct (vPlus L T) ⟨n, hn⟩ ^ 2 = 1 ∧
        ∀ s ∈ autOn T (vPlus L T), conjAct (vPlus L T) ⟨n, hn⟩ * s =
          s * conjAct (vPlus L T) ⟨n, hn⟩ := by
    intro g hg hnle
    set N := (tC L T).map (MulAut.conj g).toMonoidHom with hNdef
    have hNT : N ≤ T := map_conj_le_of_le (inf_le_left) hg
    have hTN : T ≤ Subgroup.normalizer (N : Set G) := le_normalizer_map_conj hg hTTC
    have hNV : N ≤ Subgroup.normalizer (vPlus L T : Set G) := hNT.trans hTV
    have hne : autOn N (vPlus L T) ≠ ⊥ := by
      intro hb
      apply hnle
      show N ≤ pCoreOf 2 (L ⊔ T)
      rw [← hCQ]
      intro n hn
      refine Subgroup.mem_inf.mpr ⟨hNT hn, ?_⟩
      have h1 : conjAct (vPlus L T) ⟨n, hNV hn⟩ = 1 := by
        have : conjAct (vPlus L T) ⟨n, hNV hn⟩ ∈ autOn N (vPlus L T) :=
          CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨n, hNV hn⟩, hn, rfl⟩
        rw [hb, Subgroup.mem_bot] at this
        exact this
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := congrArg (fun φ : MulAut ↥(vPlus L T) => ((φ ⟨v, hv⟩ : ↥(vPlus L T)) : G)) h1
      simp only [InternalSec.coe_conjAct_apply, MulAut.one_apply] at this
      calc v * n = (n * v * n⁻¹) * n := by rw [this]
        _ = n * v := by group
    obtain ⟨z, hz, hz1, hz2, hzc⟩ := exists_central_involution hS2
      (InternalSec.autOn_le_autOn_of_le hNT)
      (le_normalizer_of_conj (InternalSec.autOn_normal_of (U := vPlus L T) hTN)) hne
    obtain ⟨⟨n, hn⟩, hnN, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hz
    exact ⟨n, hnN, hn, hz1, hz2, hzc⟩
  obtain ⟨n₁, hn₁, hv₁, hz₁, hz₁2, hzc₁⟩ := key d⁻¹ (inv_mem hdT) h₁
  obtain ⟨n₂, hn₂, hv₂, hz₂, hz₂2, hzc₂⟩ := key d⁻¹⁻¹ (inv_mem (inv_mem hdT)) h₂'
  have hcY : ∀ {N : Subgroup G} {n : G} (hv : n ∈ Subgroup.normalizer (vPlus L T : Set G)),
      n ∈ N → (∀ x ∈ N, ∀ y ∈ Y, x * y = y * x) →
      ∀ y ∈ autOn Y (vPlus L T), conjAct (vPlus L T) ⟨n, hv⟩ * y =
        y * conjAct (vPlus L T) ⟨n, hv⟩ := by
    intro N n hv hnN hNY y hy
    obtain ⟨g, hg, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hy
    rw [← map_mul, ← map_mul, show (⟨n, hv⟩ : Subgroup.normalizer (vPlus L T : Set G)) * g =
      g * ⟨n, hv⟩ from Subtype.ext (hNY n hnN g hg)]
  have hzz := huniq _ (CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨n₁, hv₁⟩,
      map_conj_le_of_le inf_le_left (inv_mem hdT) hn₁, rfl⟩)
    _ (CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨n₂, hv₂⟩,
      map_conj_le_of_le inf_le_left (inv_mem (inv_mem hdT)) hn₂, rfl⟩)
    hzc₁ hzc₂ hz₁2 hz₂2 hz₁ hz₂ (hcY hv₁ hn₁ hY₁) (hcY hv₂ hn₂ hY₂)
  obtain ⟨⟨v, hv⟩, hvz⟩ : ∃ v : ↥(vPlus L T), conjAct (vPlus L T) ⟨n₁, hv₁⟩ v ≠ v := by
    by_contra hall
    push Not at hall
    exact hz₁ (MulEquiv.ext hall)
  have hv' : n₁ * v * n₁⁻¹ ≠ v := by
    intro he
    apply hvz
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply]
    exact he
  have he₁₂ : n₁ * v * n₁⁻¹ = n₂ * v * n₂⁻¹ := by
    have := congrArg (fun φ : MulAut ↥(vPlus L T) => ((φ ⟨v, hv⟩ : ↥(vPlus L T)) : G)) hzz
    simpa only [InternalSec.coe_conjAct_apply] using this
  have hvT : v ∈ T := (hred.1.trans inf_le_left).trans
    (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) hv
  have hmem : ∀ {N : Subgroup G} {n : G}, T ≤ Subgroup.normalizer (N : Set G) → n ∈ N →
      n * v * n⁻¹ * v⁻¹ ∈ N := by
    intro N n hTN hn
    have h1 : v * n⁻¹ * v⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hTN hvT) _).mp (N.inv_mem hn)
    have e : n * v * n⁻¹ * v⁻¹ = n * (v * n⁻¹ * v⁻¹) := by group
    rw [e]
    exact N.mul_mem hn h1
  have hc₁ := hmem (le_normalizer_map_conj (inv_mem hdT) hTTC) hn₁
  have hc₂ := hmem (le_normalizer_map_conj (inv_mem (inv_mem hdT)) hTTC) hn₂
  rw [← he₁₂] at hc₂
  have h1 := h.tC_inf_conjugate_eq_bot h38 h39 hTL (D.pow_mem hdD 2) (h.sq_not_mem hdD hdM)
  have hc : d⁻¹ * (n₁ * v * n₁⁻¹ * v⁻¹) * d ∈ tC L T ⊓ CFSG.conjugate (tC L T) (d ^ 2) := by
    simp only [A38.mem_map_conj, inv_inv] at hc₁ hc₂
    refine Subgroup.mem_inf.mpr ⟨hc₂, ?_⟩
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv]
    have e : d ^ 2 * (d⁻¹ * (n₁ * v * n₁⁻¹ * v⁻¹) * d) * (d ^ 2)⁻¹ =
        d * (n₁ * v * n₁⁻¹ * v⁻¹) * d⁻¹ := by group
    rw [e]
    exact hc₁
  rw [h1, Subgroup.mem_bot] at hc
  apply hv'
  have : n₁ * v * n₁⁻¹ * v⁻¹ = 1 := by
    have := congrArg (fun x => d * x * d⁻¹) hc
    simpa [mul_assoc] using this
  calc n₁ * v * n₁⁻¹ = (n₁ * v * n₁⁻¹ * v⁻¹) * v := by group
    _ = v := by rw [this, one_mul]

end Hyp331

theorem stmt3_3_27_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h25 : Stmt3_3_25) (hL32 : FactL32CentralInv) (hInsp : Insp3_3_27) : Stmt3_3_27 := by
  intro G _ _ T M L D h d hdD hdM _ hTC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hblock := (h25 G T M L D h).1
  have hshort : IsShort2 L := by
    rcases hblock with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  have hdM' : d⁻¹ ∉ M := fun hm => hdM (by simpa using M.inv_mem hm)
  have h1 := h.tC_inf_conjugate_eq_bot h38 h39 hTL hdD hdM
  have h1' := h.tC_inf_conjugate_eq_bot h38 h39 hTL (D.inv_mem hdD) hdM'
  have hMp := Hyp331.mPlus_eq_of_le hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) (vPlus L T)) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  obtain ⟨hKX, hXK, h2X, hSyl⟩ := h.autOn_data
  rw [hMp] at hKX hXK h2X
  have h3 : CFSG.conjugate (tC L T) d ≤ qL L T ∨ tC L T ≤ CFSG.conjugate (qL L T) d := by
    by_cases hP : IsPSL 3 2 1 ↥(autOn L (vPlus L T))
    · refine h.three_of_uniq h38 h39 hTL hdD hdM (Y := ⊥) (fun x _ y hy => ?_)
        (fun x _ y hy => ?_) ?_
      · rw [Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]
      · rw [Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]
      · intro z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ _ _
        exact hL32 (MulAut ↥(vPlus L T)) (autOn (L ⊔ T) (vPlus L T)) (autOn L (vPlus L T))
          (autOn T (vPlus L T)) hKX hXK hP h2X hO2 hSyl z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂
    · obtain ⟨hDX, -, -⟩ := (h25 G T M L D h).2.1 hTC hP
      have hXL : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ L :=
        (oTwoUpper_le _).trans inf_le_left
      have hcomm : ∀ g : G, g ∈ Subgroup.normalizer
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : Set G) →
          ∀ x ∈ (tC L T).map (MulAut.conj g⁻¹).toMonoidHom,
          ∀ y ∈ oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
            x * y = y * x := by
        intro g hg x hx y hy
        rw [A38.mem_map_conj, inv_inv] at hx
        have hy' := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
        have hc : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ (hXL hy')
        calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [hc]
          _ = y * x := by group
      refine h.three_of_uniq h38 h39 hTL hdD hdM (Y := oTwoUpper (L ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G))) (hcomm d (hDX hdD)) ?_ ?_
      · intro x hx y hy
        exact hcomm d⁻¹ (inv_mem (hDX hdD)) x hx y hy
      · intro z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
        exact hInsp G T M L D h hTL hblock hP z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
  refine ⟨h1, ?_, h3⟩
  by_contra hΦ
  have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hF := h.frattini_qL_le_tC h38 h39 hshort hTL
  have hcase : ∀ g : G, (tC L T).map (MulAut.conj g).toMonoidHom ≤ qL L T →
      tC L T ⊓ (tC L T).map (MulAut.conj g).toMonoidHom = ⊥ → False := by
    intro g hle hinf
    apply hΦ
    rw [← frattini_map_conj_eq_bot_iff g]
    have hle' : (frattini ↥((tC L T).map (MulAut.conj g).toMonoidHom)).map
        ((tC L T).map (MulAut.conj g).toMonoidHom).subtype ≤ ⊥ := by
      rw [← hinf]
      exact le_inf ((frattini_map_mono hQ2 hle).trans hF) (Subgroup.map_subtype_le _)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp
      (le_bot_iff.mp hle')
  rcases h3 with h3 | h3
  · exact hcase d⁻¹ h3 h1
  · refine hcase d⁻¹⁻¹ ?_ h1'
    intro x hx
    rw [A38.mem_map_conj, inv_inv] at hx
    have := h3 hx
    rw [CFSG.conjugate, A38.mem_map_conj, inv_inv] at this
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13
