module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.StandardType.TableBUE

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem ufe_eq_one_of_ggLAut_eq_one {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {N : ℕ} {K : Type} [Field K] [Finite K]
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (unitarySU 2 1 K N))
    (hHp : commutator H = ⊤) (hEab : IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    {b : G} (hb : b ∈ E) (h1 : ggLAut H θ ⟨b, hEN hb⟩ = 1) : b = 1 := by
  have hcent : b ∈ Subgroup.centralizer (H : Set G) :=
    mem_centralizer_of_ggLAut_eq_one H θ hHp h1
  let c : ↥(Subgroup.centralizer (H : Set G)) := ⟨b, hcent⟩
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    show b ^ 3 = 1
    exact hEab.2 b hb
  have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hdiv : orderOf c ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) := orderOf_dvd_natCard c
  have hone : orderOf c = 1 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf c) hord with h | h
    · exact h
    · exact absurd (h ▸ hdiv) hC3
  have hc : c = 1 := orderOf_eq_one_iff.mp hone
  have hc' : (c : G) = 1 := congrArg Subtype.val hc
  rw [show (c : G) = b from rfl] at hc'
  exact hc'

private theorem ufe_card_Vfull (N : ℕ) (hN : 1 ≤ N) :
    Nat.card (UnitRaw.Vfull N) = 3 ^ (N - 1) := by
  have hdim : Module.finrank UnitRaw.F (UnitRaw.Vfull N) = N - 1 := by
    show Module.finrank UnitRaw.F (UnitRaw.W N ⧸ UnitRaw.oneLine N) = N - 1
    rw [Submodule.finrank_quotient]
    have hW : Module.finrank UnitRaw.F (UnitRaw.W N) = N := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hline : Module.finrank UnitRaw.F (UnitRaw.oneLine N) = 1 := by
      rw [UnitRaw.oneLine]
      exact finrank_span_singleton (K := UnitRaw.F) (v := fun _ : Fin N => (1 : UnitRaw.F))
        (by
          intro h
          have h' := congrFun h ⟨0, by omega⟩
          simp at h')
    rw [hW, hline]
  rw [Module.natCard_eq_pow_finrank (K := UnitRaw.F) (V := UnitRaw.Vfull N), hdim]
  congr 1
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card 3


private theorem ufe_threshold {N M : ℕ} (hN4 : 4 ≤ N) (hcard : 3 ^ 4 ≤ M)
    (hrk : 3 ∣ N → 3 ^ (N - 3) ≤ M) (h3 : 3 ∣ N) : 3 ^ (N / 3 + 2) ≤ M := by
  have h6le : 6 ≤ N := by
    obtain ⟨k, rfl⟩ := h3
    omega
  rcases eq_or_ne N 6 with h6 | h6
  · subst h6
    simpa using hcard
  · have h9 : 9 ≤ N := by
      obtain ⟨k, rfl⟩ := h3
      omega
    have h2 : 3 ^ 3 ≤ M :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard
    exact LineU.card_ge_of_dvd (p := 3) (d := N) (N := M) Nat.prime_three (by norm_num)
      (by omega) h3 (by omega) (hrk h3) h2

private theorem ufe_torality {K : Type} [Field K] [Finite K] {N : ℕ}
    (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = 4) (hN : 4 ≤ N)
    (Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 1 K N))))
    (hAb : IsElemAbelian 3 Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K N))
      (LargeEvenGUSet (Fin N) K (2 ^ 1)))
    (hcard : 3 ^ 4 ≤ Nat.card Ab) (hrk : 3 ∣ N → 3 ^ (N - 3) ≤ Nat.card Ab) :
    ∃ P ∈ primeFormUnitary h (idGram K N), ∀ a ∈ Ab, ∃ (M : GL (Fin N) K)
      (hM : M ∈ LargeEvenGUSet (Fin N) K (2 ^ 1)),
      ((P⁻¹ * M * P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 1 K N) ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
  have hd : 3 ≤ N := by omega
  have hdq : (N, 2 ^ 1) ≠ (3, 2) := by
    intro he
    have h := congrArg Prod.fst he
    simp only at h
    omega
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  by_cases h3 : 3 ∣ N
  · exact TableBUD.exists_unitary_frame h hK hd hdq Nat.prime_three hpq hAb hAbI
      (ufe_threshold hN hcard hrk h3)
  · exact TableBUD.exists_unitary_frame_coprime h hK hd hdq Nat.prime_three hpq h3 hAb hAbI

theorem existsUnitFrame_holds : ExistsUnitFrame := by
  intro G _ _ H E N K _ _ θ hK hN4 hHp hEab hEN hI hC3 hcard hrk
  classical
  obtain ⟨ζ, hζ⟩ := exists_injective_zeta (K := K) hK
  have hζsurj : Function.Surjective ζ := zeta_surjective ζ hK hζ
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  let En : Subgroup ↥(Subgroup.normalizer (H : Set G)) :=
    E.subgroupOf (Subgroup.normalizer (H : Set G))
  let fE : ↥En →* MulAut (LargeEvenProj (unitarySU 2 1 K N)) :=
    (ggLAut H θ).comp En.subtype
  let Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 1 K N))) := En.map (ggLAut H θ)
  have hfE_inj : Function.Injective fE := by
    intro x y hxy
    have h1 : ggLAut H θ (x : Subgroup.normalizer (H : Set G)) =
        ggLAut H θ (y : Subgroup.normalizer (H : Set G)) := hxy
    have h2 : ggLAut H θ (((x : Subgroup.normalizer (H : Set G)) *
        ((y : Subgroup.normalizer (H : Set G)))⁻¹ : Subgroup.normalizer (H : Set G))) = 1 := by
      rw [map_mul, map_inv, h1]
      simp
    have hmem : (((x : Subgroup.normalizer (H : Set G)) *
        ((y : Subgroup.normalizer (H : Set G)))⁻¹ : Subgroup.normalizer (H : Set G)) : G) ∈ E := by
      change ((x : Subgroup.normalizer (H : Set G)) : G) *
        (((y : Subgroup.normalizer (H : Set G)) : G))⁻¹ ∈ E
      exact E.mul_mem (Subgroup.mem_subgroupOf.mp x.2)
        (E.inv_mem (Subgroup.mem_subgroupOf.mp y.2))
    have h3 := ufe_eq_one_of_ggLAut_eq_one θ hHp hEab hEN hC3 hmem h2
    have h4 : x * y⁻¹ = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h3
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h4]
      _ = y := one_mul y
  have hAb_range : Ab = fE.range := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      exact MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩
    · intro ha
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
      exact Subgroup.mem_map.mpr ⟨(b : Subgroup.normalizer (H : Set G)), b.2, rfl⟩
  have hAb_card : Nat.card ↥Ab = Nat.card ↥E := by
    rw [hAb_range, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfE_inj,
      Subgroup.card_top]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hAb_elem : IsElemAbelian 3 Ab :=
    (hEab.subgroupOf (Subgroup.normalizer (H : Set G))).map (ggLAut H θ)
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K N))
      (LargeEvenGUSet (Fin N) K (2 ^ 1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hb_eq : (⟨((b : Subgroup.normalizer (H : Set G)) : G), hEN hb⟩ :
        Subgroup.normalizer (H : Set G)) = b := Subtype.ext rfl
    rw [← hb_eq]
    exact hI ((b : Subgroup.normalizer (H : Set G)) : G) (Subgroup.mem_subgroupOf.mp hb)
  have hmem_Ab : ∀ b : ↥E, ggLAut H θ ⟨(b : G), hEN b.2⟩ ∈ Ab := by
    intro b
    exact Subgroup.mem_map.mpr ⟨⟨(b : G), hEN b.2⟩, Subgroup.mem_subgroupOf.mp b.2, rfl⟩
  obtain ⟨P, hP, hframe⟩ := ufe_torality (K := K) (N := N)
    h hK hN4 Ab hAb_elem hAbI
    (by rwa [hAb_card]) (fun h3 => by rw [hAb_card]; exact hrk h3)
  have hstep4 : ∀ b : ↥E, ∃ M : GL (Fin N) K, ∃ hM : M ∈ LargeEvenGUSet (Fin N) K (2 ^ 1),
      ((P⁻¹ * M * P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).IsDiag ∧
        ggLAut H θ ⟨(b : G), hEN b.2⟩ =
          TableB.projConj (unitarySU 2 1 K N) ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
    intro b
    obtain ⟨M, hM, hdiag, heq⟩ := hframe _ (hmem_Ab b)
    exact ⟨M, hM, hdiag, heq⟩
  choose M hM hdiag heq using hstep4
  choose wv hwv using fun b : ↥E =>
    exists_diagOf_eq ζ hζsurj (P⁻¹ * M b * P) (hdiag b)
  let π : ↥H →* LargeEvenProj (unitarySU 2 1 K N) :=
    (conjProj h P hP).toMonoidHom.comp
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥H)))
  have hπ_surj : Function.Surjective π := by
    intro r
    obtain ⟨s, rfl⟩ := (conjProj h P hP).surjective r
    obtain ⟨t, rfl⟩ := θ.surjective s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥H) t
    exact ⟨x, rfl⟩
  have hπ_ker : π.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have h1 : (conjProj h P hP) (θ (QuotientGroup.mk' (Subgroup.center ↥H) x)) = 1 := hx
    have h2 : θ (QuotientGroup.mk' (Subgroup.center ↥H) x) = 1 := by
      apply (conjProj h P hP).injective
      rw [h1, map_one]
    have h3 : QuotientGroup.mk' (Subgroup.center ↥H) x = 1 := θ.injective (by rw [h2, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h3
  let D : ↥E → Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    fun b => ⟨diagOf ζ (wv b), diagOf_mem_normalizer ζ h (wv b)⟩
  have hkey : ∀ (b : ↥E) (h' : ↥H),
      π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h') =
        TableB.projConj (unitarySU 2 1 K N) (D b) (π h') := by
    intro b h'
    show (conjProj h P hP) (θ (QuotientGroup.mk' (Subgroup.center ↥H)
        (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h'))) =
      TableB.projConj (unitarySU 2 1 K N) (D b)
        ((conjProj h P hP) (θ (QuotientGroup.mk' (Subgroup.center ↥H) h')))
    have hgg : θ (QuotientGroup.mk' (Subgroup.center ↥H)
          (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h')) =
        ggLAut H θ ⟨(b : G), hEN b.2⟩
          (θ (QuotientGroup.mk' (Subgroup.center ↥H) h')) := by
      simpa only [QuotientGroup.mk'_apply] using
        (ggLAut_apply H θ ⟨(b : G), hEN b.2⟩ h').symm
    rw [hgg, heq b]
    have hMN : M b ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      TableBUE.gu_subset_normalizer h (hM b)
    have hPN : P ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      CFSG.StandardType.LineU.primeForm_mem_normalizer h hP
    have hDN : P⁻¹ * M b * P ∈
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    rw [TableBUD.conjProj_projConj h P hP
      ⟨M b, TableBUE.gu_subset_normalizer h (hM b)⟩ hDN]
    rw [show D b = ⟨P⁻¹ * M b * P, hDN⟩ from Subtype.ext (hwv b)]
  let f : ↥E → UnitRaw.Vfull N := fun b => (UnitRaw.oneLine N).mkQ (wv b)
  have hf_add : ∀ b₁ b₂ : ↥E, f (b₁ * b₂) = f b₁ + f b₂ := by
    intro b₁ b₂
    have hnm : (⟨((b₁ * b₂ : ↥E) : G), hEN (b₁ * b₂).2⟩ :
        Subgroup.normalizer (H : Set G)) =
        ⟨(b₁ : G), hEN b₁.2⟩ * ⟨(b₂ : G), hEN b₂.2⟩ := Subtype.ext rfl
    have hmul : TableB.projConj (unitarySU 2 1 K N) (D (b₁ * b₂)) =
        TableB.projConj (unitarySU 2 1 K N) (D b₁) *
          TableB.projConj (unitarySU 2 1 K N) (D b₂) := by
      ext r
      obtain ⟨h', rfl⟩ := hπ_surj r
      rw [MulAut.mul_apply, ← hkey b₂ h',
        ← hkey b₁ (H.normalizerMonoidHom ⟨(b₂ : G), hEN b₂.2⟩ h'),
        ← hkey (b₁ * b₂) h']
      rw [hnm, map_mul, MulAut.mul_apply]
    have hclass : (UnitRaw.oneLine N).mkQ (wv (b₁ * b₂)) =
        (UnitRaw.oneLine N).mkQ (wv b₁ + wv b₂) := by
      apply (projConj_diagOf_eq_iff ζ h hK hζ hN4 (wv (b₁ * b₂))
        (wv b₁ + wv b₂)).mp
      have hDmul : D b₁ * D b₂ =
          ⟨diagOf ζ (wv b₁ + wv b₂),
            diagOf_mem_normalizer ζ h (wv b₁ + wv b₂)⟩ := by
        apply Subtype.ext
        change diagOf ζ (wv b₁) * diagOf ζ (wv b₂) = diagOf ζ (wv b₁ + wv b₂)
        exact (diagOf_add ζ (wv b₁) (wv b₂)).symm
      rw [← map_mul, hDmul] at hmul
      exact hmul
    show (UnitRaw.oneLine N).mkQ (wv (b₁ * b₂)) =
      (UnitRaw.oneLine N).mkQ (wv b₁) + (UnitRaw.oneLine N).mkQ (wv b₂)
    rw [← map_add]
    exact hclass
  let ι : Additive ↥E →+ UnitRaw.Vfull N :=
    AddMonoidHom.mk' (fun x => f (Additive.toMul x)) (fun a b => by
      show f (Additive.toMul (a + b)) =
        f (Additive.toMul a) + f (Additive.toMul b)
      rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl]
      exact hf_add _ _)
  have hι_inj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hzero : (UnitRaw.oneLine N).mkQ (wv (Additive.toMul x)) = 0 := hx
    have hmem : wv (Additive.toMul x) ∈ UnitRaw.oneLine N :=
      (Submodule.Quotient.mk_eq_zero (UnitRaw.oneLine N)).mp hzero
    have hD1 : TableB.projConj (unitarySU 2 1 K N) (D (Additive.toMul x)) = 1 :=
      (projConj_diagOf_eq_one_iff ζ h hK hζ hN4 (wv (Additive.toMul x))).mpr hmem
    have hgg : ggLAut H θ ⟨((Additive.toMul x : ↥E) : G), hEN (Additive.toMul x).2⟩ = 1 := by
      apply MulEquiv.ext
      intro r
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥H) q
      have h1 : (conjProj h P hP) (θ (↑(H.normalizerMonoidHom ⟨((Additive.toMul x : ↥E) : G),
              hEN (Additive.toMul x).2⟩ h') : ↥H ⧸ Subgroup.center ↥H)) =
          (conjProj h P hP) (θ (↑h' : ↥H ⧸ Subgroup.center ↥H)) := by
        have hk := hkey (Additive.toMul x) h'
        rw [hD1] at hk
        simpa [π, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply] using hk
      have h2 := (conjProj h P hP).injective h1
      have h3 : (↑(H.normalizerMonoidHom ⟨((Additive.toMul x : ↥E) : G),
            hEN (Additive.toMul x).2⟩ h') : ↥H ⧸ Subgroup.center ↥H) = ↑h' := θ.injective h2
      rw [QuotientGroup.mk'_apply, ggLAut_apply, h3]
      rfl
    have hb1 : ((Additive.toMul x : ↥E) : G) = 1 :=
      ufe_eq_one_of_ggLAut_eq_one θ hHp hEab hEN hC3 (Additive.toMul x).2 hgg
    have hb : Additive.toMul x = 1 := Subtype.ext hb1
    exact Additive.toMul.injective (by simpa using hb)
  have hInter : ∀ (b : ↥E) (w : UnitRaw.W N),
      (UnitRaw.oneLine N).mkQ w = ι (Additive.ofMul b) →
      ∃ hD : diagOf ζ w ∈
          Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)),
        ∀ h' : ↥H, π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h') =
          TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ (π h') := by
    intro b w hw
    refine ⟨diagOf_mem_normalizer ζ h w, fun h' => ?_⟩
    have hclass : (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ (wv b) := by
      rw [hw]
      rfl
    have hproj : TableB.projConj (unitarySU 2 1 K N) (D b) =
        TableB.projConj (unitarySU 2 1 K N)
          ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ :=
      (projConj_diagOf_eq_iff ζ h hK hζ hN4 (wv b) w).mpr hclass.symm
    rw [hkey b h', hproj]
  have h5 : 5 ≤ N := by
    have hcardV : Nat.card ↥E ≤ Nat.card (UnitRaw.Vfull N) := by
      have h1 : Nat.card (Additive ↥E) ≤ Nat.card (UnitRaw.Vfull N) :=
        Nat.card_le_card_of_injective ι hι_inj
      rwa [Nat.card_congr Additive.toMul] at h1
    rw [ufe_card_Vfull N (by omega)] at hcardV
    have h4 : 3 ^ 4 ≤ 3 ^ (N - 1) := le_trans hcard hcardV
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h4
    omega
  let fr : UnitFrame H E hEN K N ζ :=
    { π := π
      surj := hπ_surj
      ker_le := hπ_ker
      ι := ι
      inj := hι_inj
      intertwine := hInter }
  exact ⟨ζ, hζ, h5, ⟨fr⟩⟩

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
