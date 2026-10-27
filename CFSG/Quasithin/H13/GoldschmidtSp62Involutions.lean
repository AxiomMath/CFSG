module

public import CFSG.Quasithin.H13.GoldschmidtSp62Base
public import CFSG.Quasithin.H13.U3S1349F
public import Certificates.Certificate4195
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U CFSG.Blueprint
  CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

theorem sp62X1_check : sp62X1OK = true :=
  Certificates.certificate4195

theorem sp62X1_parts :
    sp62AGens.all pairCheck = true ∧ sp62AGens.all (fun cc => sylowT.contains cc.1) = true ∧
      closureOK (sp62AGens.map Prod.fst) sp62ATab 64 = true ∧
      sp62ATab.all (fun c => mul6 c c == one6 && sp62ATab.all fun c' => commutes6 c c') = true ∧
      sp62PeelOK 62 sp62Invs sp62PeelSeq = true ∧ sp62YOK orbit0 sp62Y0 = true ∧
      sp62YOK orbit1 sp62Y1 = true ∧ sp62YOK orbit2 sp62Y2 = true ∧
      sp62YOK orbit3 sp62Y3 = true := by
  have h := sp62X1_check
  simp only [sp62X1OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem sp62PeelOK_spec {α : Type*} {d : ℕ} (code : α → List ℕ) :
    ∀ (peel R : List (List ℕ)), sp62PeelOK d R peel = true →
      ∀ S : Finset α, Set.InjOn code S → (∀ s ∈ S, code s ∈ R) →
        (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → commutes6 (code s) (code s') = true) → d < S.card →
        ∀ s ∈ S, code s ∈ sp62PeelRes R peel := by
  classical
  intro peel
  induction peel with
  | nil =>
    intro R _ S _ hR _ _ s hs
    simpa [sp62PeelRes] using hR s hs
  | cons v rest ih =>
    intro R hok S hinj hR hcomm hcard
    simp only [sp62PeelOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hv, hlen⟩, hrest⟩ := hok
    have hvS : ∀ s ∈ S, code s ≠ v := by
      intro s₀ hs₀ hcode
      have hsub : (S.erase s₀).image code ⊆
          (R.filter fun w => !(w == v) && commutes6 v w).toFinset := by
        intro w hw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hsne, hsS⟩ := Finset.mem_erase.mp hs
        simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq]
        refine ⟨hR s hsS, ?_, ?_⟩
        · intro h
          exact hsne (hinj hsS hs₀ (h.trans hcode.symm))
        · rw [← hcode]
          exact hcomm s₀ hs₀ s hsS (Ne.symm hsne)
      have h1 : ((S.erase s₀).image code).card = (S.erase s₀).card :=
        Finset.card_image_of_injOn (hinj.mono fun x hx => Finset.mem_of_mem_erase hx)
      have h2 : (S.erase s₀).card = S.card - 1 := Finset.card_erase_of_mem hs₀
      have h3 := Finset.card_le_card hsub
      have h4 := List.toFinset_card_le (R.filter fun w => !(w == v) && commutes6 v w)
      omega
    refine ih (R.erase v) hrest S hinj (fun s hs => ?_) hcomm hcard
    exact (List.mem_erase_of_ne (hvS s hs)).mpr (hR s hs)

theorem exists_code_SH {g : H6} (hg : g ∈ SH) :
    ∃ c ∈ sylowT, dec6 c = mat6 g ∧ canon6 c = true := by
  obtain ⟨t, ht, hcode, hcan⟩ := exists_code_closure sylowP sylowP_check 512 sylowOK_parts.1 hg
  refine ⟨(closureT (sylowP.map Prod.fst)).getD t [], ?_, hcode, hcan⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
  exact Array.getElem_mem ht

theorem sp62_le_centralizer_of_core
    {B : Subgroup H6} (hBS : B ≤ SH) (hBab : IsElemAbelian 2 B) (hB : 64 ≤ Nat.card B)
    {c : List ℕ} (hc : ∀ w ∈ sp62PeelRes sp62Invs sp62PeelSeq, commutes6 w c = true) {y : H6}
    (hy : mat6 y = dec6 c) : B ≤ Subgroup.centralizer ({y} : Set H6) := by
  classical
  have hpeel : sp62PeelOK 62 sp62Invs sp62PeelSeq = true := sp62X1_parts.2.2.2.2.1
  let cd : H6 → List ℕ := fun g =>
    if h : g ∈ SH then (exists_code_SH h).choose else []
  have hcd : ∀ g ∈ SH, cd g ∈ sylowT ∧ dec6 (cd g) = mat6 g ∧ canon6 (cd g) = true := by
    intro g hg
    simp only [cd, hg, ↓reduceDIte]
    exact (exists_code_SH hg).choose_spec
  have hinj : ∀ g ∈ SH, ∀ g' ∈ SH, cd g = cd g' → g = g' := by
    intro g hg g' hg' h
    apply mat6_injective
    rw [← (hcd g hg).2.1, ← (hcd g' hg').2.1, h]
  have : Fintype ↥B := Fintype.ofFinite _
  let code : ↥B → List ℕ := fun b => cd (b : H6)
  let S : Finset ↥B := Finset.univ.erase 1
  have hSB : ∀ b : ↥B, (b : H6) ∈ SH := fun b => hBS b.2
  have hcode_inj : Set.InjOn code (S : Set ↥B) := by
    intro b _ b' _ h
    exact Subtype.ext (hinj _ (hSB b) _ (hSB b') h)
  have hSinv : ∀ b ∈ S, code b ∈ sp62Invs := by
    intro b hb
    have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
    obtain ⟨hmem, hdec, hcan⟩ := hcd _ (hSB b)
    have hsq : (b : H6) * b = 1 := by
      have := hBab.2 b b.2
      rwa [pow_two] at this
    have hcsq : mul6 (code b) (code b) = one6 := by
      refine dec6_injective (canon6_mul6 _ _) canon6_one6 ?_
      rw [dec6_mul6, show dec6 (code b) = mat6 (b : H6) from hdec, ← map_mul, hsq, map_one,
        dec6_one6]
    have hc1 : code b ≠ one6 := by
      intro h
      apply hb1
      apply Subtype.ext
      apply mat6_injective
      rw [← hdec]
      change dec6 (code b) = mat6 (1 : H6)
      rw [h, dec6_one6, map_one]
    simp only [sp62Invs, List.mem_filter, Array.mem_toList_iff, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    exact ⟨hmem, hcsq, hc1⟩
  have hScard : 62 < S.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  have hScomm : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → commutes6 (code b) (code b') = true := by
    intro b _ b' _ _
    refine commutes6_of_commute (hcd _ (hSB b)).2.1.symm (hcd _ (hSB b')).2.1.symm ?_
    have := hBab.1.is_comm.comm b b'
    exact congrArg Subtype.val this
  have hres := sp62PeelOK_spec code _ _ hpeel S hcode_inj hSinv hScomm hScard
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hb1 : b = 1
  · rw [hb1]
    simp
  · have hbS : (⟨b, hb⟩ : ↥B) ∈ S := Finset.mem_erase.mpr ⟨fun h => hb1 (congrArg Subtype.val h),
      Finset.mem_univ _⟩
    exact commute_of_commutes6 (hcd b (hBS hb)).2.1.symm hy (hc _ (hres _ hbS))

theorem sp62_exists_A :
    ∃ A : Subgroup H6, A ≤ SH ∧ IsElemAbelian 2 A ∧ Nat.card A = 64 := by
  obtain ⟨hpair, hsyl, hcl, hab, -⟩ := sp62X1_parts
  refine ⟨Subgroup.closure (genSet sp62AGens hpair), ?_, ?_, card_closure_genSet _ _ _ hcl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨cc, hm, rfl⟩
    have hc : cc.1 ∈ sylowT := by
      have := List.all_eq_true.mp hsyl cc hm
      simpa using this
    exact mem_closure_of_mem_table sylowP sylowP_check 512 sylowOK_parts.1 hc
      (mat6_ofCode cc _)
  · have hcode : ∀ a ∈ Subgroup.closure (genSet sp62AGens hpair), ∃ c ∈ sp62ATab,
        dec6 c = mat6 a := by
      intro a ha
      obtain ⟨t, ht, hdec, -⟩ := exists_code_closure sp62AGens hpair 64 hcl ha
      refine ⟨(closureT (sp62AGens.map Prod.fst)).getD t [], ?_, hdec⟩
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
      exact Array.getElem_mem ht
    have hab' : ∀ c ∈ sp62ATab, mul6 c c = one6 ∧ ∀ c' ∈ sp62ATab, commutes6 c c' = true := by
      intro c hc
      have h1 := (Array.all_eq_true_iff_forall_mem.mp hab) c hc
      rw [Bool.and_eq_true, beq_iff_eq] at h1
      exact ⟨h1.1, Array.all_eq_true_iff_forall_mem.mp h1.2⟩
    refine ⟨⟨⟨fun a a' => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨c, hc, hca⟩ := hcode a a.2
      obtain ⟨c', hc', hca'⟩ := hcode a' a'.2
      exact Subtype.ext (commute_of_commutes6 hca.symm hca'.symm ((hab' c hc).2 c' hc'))
    · obtain ⟨c, hc, hca⟩ := hcode a ha
      have hsq : a * a = 1 := by
        apply mat6_injective
        rw [map_mul, ← hca, ← dec6_mul6, (hab' c hc).1, dec6_one6, map_one]
      rw [pow_two, hsq]

theorem sp62_exists_y_aux
    {i : Fin 4} {c : List ℕ} (hc : sp62YOK (orbTab i) c = true) :
    ∃ y : H6, (∃ g : H6, y = g * tH i * g⁻¹) ∧
      thompsonJ SH ≤ Subgroup.centralizer ({y} : Set H6) := by
  obtain ⟨A, hAS, hAab, hA64⟩ := sp62_exists_A
  simp only [sp62YOK, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨hpair, hfound⟩, hcore⟩ := hc
  refine ⟨ofCode (c, c) hpair, ?_, ?_⟩
  · exact eq_conj_of_found i (mat6_ofCode (c, c) hpair) hfound
  · refine iSup₂_le fun B hB => ?_
    obtain ⟨hBS, hBab, hBmax⟩ := hB
    have hB64 : 64 ≤ Nat.card B := hA64 ▸ hBmax A hAS hAab
    exact sp62_le_centralizer_of_core hBS hBab hB64 (fun w hw => hcore w hw)
      (mat6_ofCode (c, c) hpair)

theorem sp62_exists_y (i : Fin 4) :
    ∃ y : H6, (∃ g : H6, y = g * tH i * g⁻¹) ∧
      thompsonJ SH ≤ Subgroup.centralizer ({y} : Set H6) := by
  obtain ⟨-, -, -, -, -, h0, h1, h2, h3⟩ := sp62X1_parts
  fin_cases i
  · exact sp62_exists_y_aux h0
  · exact sp62_exists_y_aux h1
  · exact sp62_exists_y_aux h2
  · exact sp62_exists_y_aux h3

theorem sp62InvolutionsIntoCJ_H6
    (P : Sylow 2 H6) {x : H6} (hx : orderOf x = 2) :
    ∃ g : H6, g * x * g⁻¹ ∈ Subgroup.centralizer (thompsonJ (P : Subgroup H6) : Set H6) := by
  obtain ⟨i, g₁, hg₁⟩ := exists_conj_of_sylow_classes SH_isPGroup SH_index exists_conj_of_mem_SH hx
  obtain ⟨y, ⟨g₂, hy⟩, hJ⟩ := sp62_exists_y i
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H6 (SH_isPGroup.toSylow SH_index) P
  have hPeq : (P : Subgroup H6) = SH.map (MulAut.conj h).toMonoidHom := by
    have h1 : ((h • SH_isPGroup.toSylow SH_index : Sylow 2 H6) : Subgroup H6) =
        (P : Subgroup H6) := by rw [hh]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  have hJP : thompsonJ (P : Subgroup H6) = (thompsonJ SH).map (MulAut.conj h).toMonoidHom := by
    rw [hPeq]
    exact AmalTransport.thompsonJ_map_of_injective _ (MulAut.conj h).injective SH
  refine ⟨h * g₂ * g₁⁻¹, ?_⟩
  have hxy : h * g₂ * g₁⁻¹ * x * (h * g₂ * g₁⁻¹)⁻¹ = h * y * h⁻¹ := by
    rw [hg₁, hy]
    group
  rw [hxy, Subgroup.mem_centralizer_iff, hJP]
  rintro _ ⟨w, hw, rfl⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp (hJ hw)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc h * w * h⁻¹ * (h * y * h⁻¹) = h * (w * y) * h⁻¹ := by group
    _ = h * (y * w) * h⁻¹ := by rw [this]
    _ = h * y * h⁻¹ * (h * w * h⁻¹) := by group

theorem sp62InvolutionsIntoCJ_of :
    Sp62InvolutionsIntoCJ := by
  intro X _ _ hX P x hx
  obtain ⟨φ⟩ := nonempty_mulEquiv_statedSp_of_lieModel hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx' : orderOf (φ x) = 2 := (MulEquiv.orderOf_eq φ x).trans hx
  obtain ⟨g', hg'⟩ := sp62InvolutionsIntoCJ_H6 (P.mapSurjective (f := φ.toMonoidHom) φ.surjective)
    hx'
  have hJ : thompsonJ ((P : Subgroup X).map φ.toMonoidHom) =
      (thompsonJ (P : Subgroup X)).map φ.toMonoidHom :=
    AmalTransport.thompsonJ_map_of_injective _ φ.injective _
  refine ⟨φ.symm g', ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hφw : φ w ∈ thompsonJ ((P : Subgroup X).map φ.toMonoidHom) := by
    rw [hJ]
    exact ⟨w, hw, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp
    (by simpa [Sylow.coe_mapSurjective] using hg') (φ w) (by simpa using hφw)
  apply φ.injective
  simpa [map_mul] using h1

end CFSG.Quasithin.H13.U3
