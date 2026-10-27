module

public import CFSG.Quasithin.Vol2.Ch12Sec5L9a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St
open scoped IsMulCommutative

namespace S125L9

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem cj_le_cj {g : G} {A B : Subgroup G} (h : A ≤ B) : B3.cj g A ≤ B3.cj g B :=
  Subgroup.map_mono h

omit [Finite G] in
theorem cj_cj (a b : G) (X : Subgroup G) : B3.cj a (B3.cj b X) = B3.cj (a * b) X := by
  ext x
  rw [B3.mem_cj, B3.mem_cj, B3.mem_cj]
  constructor <;> intro hx <;> convert hx using 1 <;> group

omit [Finite G] in
theorem cj_inv_cj (a : G) (X : Subgroup G) : B3.cj a⁻¹ (B3.cj a X) = X := by
  rw [cj_cj, inv_mul_cancel]
  ext x
  rw [B3.mem_cj]
  simp

omit [Finite G] in
theorem cj_cj_inv (a : G) (X : Subgroup G) : B3.cj a (B3.cj a⁻¹ X) = X := by
  rw [cj_cj, mul_inv_cancel]
  ext x
  rw [B3.mem_cj]
  simp

omit [Finite G] in
theorem cj_inf (g : G) (A B : Subgroup G) : B3.cj g (A ⊓ B) = B3.cj g A ⊓ B3.cj g B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

omit [Finite G] in
theorem cj_centralizer (g : G) (A : Subgroup G) :
    B3.cj g (Subgroup.centralizer (A : Set G)) = Subgroup.centralizer (B3.cj g A : Set G) := by
  ext x
  rw [B3.mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := h _ (B3.mem_cj.1 hy)
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = x * y := by group
  · intro h y hy
    have h1 := h (g * y * g⁻¹) (B3.mem_cj.2 (by simpa [mul_assoc] using hy))
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * y := by group

omit [Finite G] in
theorem cj_eq_self_of_mem_normalizer {g : G} {X : Subgroup G}
    (h : g ∈ Subgroup.normalizer (X : Set G)) : B3.cj g X = X := by
  ext x
  rw [B3.mem_cj]
  have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ h) x)
  rw [inv_inv] at h1
  exact h1.symm

omit [Finite G] in
theorem cj_conjugate (m g : G) (X : Subgroup G) :
    B3.cj m (CFSG.conjugate X g) = CFSG.conjugate X (g * m⁻¹) := by
  ext x
  rw [B3.mem_cj]
  change m⁻¹ * x * m ∈ conjSubgroup X g ↔ x ∈ conjSubgroup X (g * m⁻¹)
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem part2 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) (h7 : Concl12_5_7 T L V) :
    ∀ g : G, CFSG.conjugate F.V1 g ≤ V →
      ∃ l ∈ L, CFSG.conjugate F.V1 g = CFSG.conjugate F.V1 l := by
  intro g hgV
  by_contra hP
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hV : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hE : E6.HypE61 T M V :=
    S125L6a.hypE61_of_hyp h331 h1222 h323 h3228 hyp hV hyp.irrPlus.2.1 hf.le_T hf.T_le
      hf.normalizes
  have hTM : T ≤ M := hyp.normalizes
  set P := CFSG.conjugate F.V1 g with hPdef
  have hP2 : Nat.card P = 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans (S125L9a.card_V1 F)
  have hP1 : P ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hP2; norm_num at hP2
  have hCMN : M ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    E6.inf_centralizer_le_normalizer hE hgV hP1
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two (M ⊓ Subgroup.centralizer (P : Set G))
  have hSS : QuasithinUnique.IsSylowTwoOf S (M ⊓ Subgroup.centralizer (P : Set G)) :=
    ⟨hS.1, hS.2.1, hS.2.2⟩
  have hidx : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (V : Set G))).index := by
    intro h2
    apply hyp.sylow.2
    rw [← Subgroup.relIndex_mul_index hf.T_le]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨m, hmN, hm⟩ := B3.exists_conj_le_sylow_sub hf.T_le hyp.sylow.1 hidx
    (hS.1.trans hCMN) hS.2.1
  have hmM : m ∈ M := hE.normalizer_le hmN
  set P' := B3.cj m P with hP'def
  have hP'eq : P' = CFSG.conjugate F.V1 (g * m⁻¹) := cj_conjugate m g F.V1
  have hP'V : P' ≤ V := (cj_le_cj hgV).trans (cj_eq_self_of_mem_normalizer hmN).le
  have hP'2 : Nat.card P' = 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj m).injective).trans hP2
  have hMm : B3.cj m M = M := cj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hmM)
  have hSyl' : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (P' : Set G))
      (M ⊓ Subgroup.centralizer (P' : Set G)) := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨inf_le_inf_right _ hTM, hyp.sylow.1.to_le inf_le_left, fun Q hQ hQ2 hTQ => ?_⟩
    have hS' : B3.cj m S ≤ T ⊓ Subgroup.centralizer (P' : Set G) := by
      refine le_inf hm ?_
      rw [hP'def, ← cj_centralizer]
      exact cj_le_cj (hS.1.trans inf_le_right)
    have hMm' : B3.cj m⁻¹ M = M :=
      cj_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hmM))
    have hQ'le : B3.cj m⁻¹ Q ≤ M ⊓ Subgroup.centralizer (P : Set G) := by
      have h1 := cj_le_cj (g := m⁻¹) hQ
      rwa [cj_inf, ← cj_centralizer, cj_inv_cj, hMm'] at h1
    have hSQ' : S ≤ B3.cj m⁻¹ Q := by
      have h1 := cj_le_cj (g := m⁻¹) (hS'.trans hTQ)
      rwa [cj_inv_cj] at h1
    have h1 := (A4.isSylowTwoOf_iff_maximal.1 hSS).2.2 _ hQ'le (hQ2.map _) hSQ'
    calc Q = B3.cj m (B3.cj m⁻¹ Q) := (cj_cj_inv m Q).symm
      _ ≤ B3.cj m S := cj_le_cj h1
      _ ≤ T ⊓ Subgroup.centralizer (P' : Set G) := hS'
  have hnot' : ¬ ∃ l ∈ L, CFSG.conjugate F.V1 l = P' := by
    rintro ⟨l, hlL, hl⟩
    apply hP
    have hmem : conjAct V ⟨m, hmN⟩ ∈ autOn L V := by
      rw [← S125L6a.autOn_normalizer_eq h12210 hyp F]
      exact mem_autOn_iff_exists.mpr ⟨m, hmN, hmM, rfl⟩
    obtain ⟨l', hl'N, hl'L, hl'⟩ := mem_autOn_iff_exists.mp hmem
    have hml : ∀ v ∈ V, m * v * m⁻¹ = l' * v * l'⁻¹ := fun v hv => by
      have h := congrArg Subtype.val (DFunLike.congr_fun hl' (⟨v, hv⟩ : ↥V))
      exact h.symm
    have hP'l : P' = B3.cj l' P := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, hp, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact (hml p (hgV hp)).symm
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, hp, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hml p (hgV hp)
    refine ⟨l * l', L.mul_mem hlL hl'L, ?_⟩
    have h1 : P = B3.cj l'⁻¹ P' := by rw [hP'l, cj_inv_cj]
    rw [h1, ← hl, cj_conjugate, inv_inv]
  exact (S125L9a.part1 h331 h1222 h323 h3228 h12210 F hH h7 P' hP'V hP'2 hnot' hSyl').2.2
    (g * m⁻¹) hP'eq.symm

theorem part4 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (h8 : Concl12_5_8 T L V F)
    (h3 : ∀ g : G, CFSG.conjugate F.V1 g ≤ V →
      ∃ l ∈ L, CFSG.conjugate F.V1 g = CFSG.conjugate F.V1 l) :
    ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → F.V1 ≤ CFSG.conjugate V g →
      (∃ h ∈ Subgroup.normalizer (F.V1 : Set G), CFSG.conjugate V g = CFSG.conjugate V h) ∧
        ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
  intro g _ hV1g
  have hf := S125Ex.Facts125.of h1222 hH
  have hV1V : F.V1 ≤ V := Subgroup.map_subtype_le _
  have hV1 : F.V1 ≠ ⊥ := fun h => by
    have := S125L9a.card_V1 F
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨x, hxV1, hx1⟩ := (Subgroup.bot_or_exists_ne_one F.V1).resolve_left hV1
  have hV1z := S125L9a.eq_zpowers (S125L9a.card_V1 F) hxV1 hx1
  have hxV : x ∈ V := hV1V hxV1
  have hx2 : x * x = 1 := by
    have := hf.sq x hxV
    rwa [pow_two] at this
  have hcl : {y | ∃ g' : G, g'⁻¹ * x * g' = y} ∩ (V : Set G) =
      {y | ∃ n ∈ Subgroup.normalizer (V : Set G), n⁻¹ * x * n = y} := by
    ext y
    constructor
    · rintro ⟨⟨g', rfl⟩, hy⟩
      have hle : CFSG.conjugate F.V1 g' ≤ V := by
        rw [hV1z]
        change (Subgroup.zpowers x).map (MulAut.conj g'⁻¹).toMonoidHom ≤ V
        rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        simpa [mul_assoc] using hy
      obtain ⟨l, hlL, hl⟩ := h3 g' hle
      have hy' : g'⁻¹ * x * g' ∈ CFSG.conjugate F.V1 l := by
        rw [← hl]
        change g'⁻¹ * x * g' ∈ conjSubgroup F.V1 g'
        rw [mem_conjSubgroup_iff]
        simpa [mul_assoc] using hxV1
      change g'⁻¹ * x * g' ∈ conjSubgroup F.V1 l at hy'
      rw [mem_conjSubgroup_iff, hV1z] at hy'
      rcases S125L5a.mem_zpowers_of_sq hx2 hy' with h | h
      · exfalso
        apply hx1
        calc x = g' * (l⁻¹ * (l * (g'⁻¹ * x * g') * l⁻¹) * l) * g'⁻¹ := by group
          _ = 1 := by rw [h]; group
      · refine ⟨l, hf.normalizes hlL, ?_⟩
        calc l⁻¹ * x * l = l⁻¹ * (l * (g'⁻¹ * x * g') * l⁻¹) * l := by rw [h]
          _ = g'⁻¹ * x * g' := by group
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x).1 hxV
      simpa using this
  obtain ⟨c, hc, hcV⟩ := (conjClass_inter_eq_iff_centralizer_transitive hxV).1 hcl V
    ⟨1, by ext y; simp [mem_conjSubgroup_iff]⟩ (conjSubgroup V g) ⟨g, rfl⟩ hxV (hV1g hxV1)
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.1 hc x rfl).symm
  have hcC : c ∈ Subgroup.centralizer (F.V1 : Set G) :=
    (S125L9a.mem_centralizer_iff_of_eq_zpowers hV1z c).2 hcx.symm
  have hcN : c ∈ Subgroup.normalizer (F.V1 : Set G) := Subgroup.centralizer_le_normalizer _ hcC
  refine ⟨⟨c, hcN, hcV.symm⟩, ?_⟩
  have hU := h8.2
  have hVU : V ≤ u128 V F.V1 := fun v hv => Subgroup.subset_closure ⟨1, Subgroup.one_mem _, v, hv,
    by group⟩
  have hVgU : CFSG.conjugate V g ≤ u128 V F.V1 := by
    change conjSubgroup V g ≤ _
    rw [← hcV]
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    exact Subgroup.subset_closure ⟨c⁻¹, Subgroup.inv_mem _ hcN, c * y * c⁻¹, hy, by group⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := hU.1.is_comm.comm ⟨y, hVgU hy⟩ ⟨v, hVU hv⟩
  exact congrArg Subtype.val this

end S125L9

open S125L9

theorem lemma12_5_9_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10) (h7 : Lemma12_5_7)
    (h8 : Lemma12_5_8) : Lemma12_5_9 := by
  intro G _ _ T L V F hH
  have h7' := h7 G T L V hH
  have h3 := part2 h331 h1222 h323 h3228 h12210 F hH h7'
  exact ⟨S125L9a.part1 h331 h1222 h323 h3228 h12210 F hH h7', h3,
    part4 h1222 F hH (h8 G T L V F hH) h3⟩

end CFSG.Quasithin.H13
