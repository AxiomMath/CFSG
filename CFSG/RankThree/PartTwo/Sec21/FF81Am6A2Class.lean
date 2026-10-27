module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2Cert
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Lv
public import CFSG.RankThree.PartTwo.Sec21.FF81S59Sp6

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec21.FF79

section Conj

variable {H : Type*} [Group H]

theorem map_conj_map (g₁ g₂ : H) (A : Subgroup H) :
    (A.map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj g₂).toMonoidHom =
      A.map (MulAut.conj (g₂ * g₁)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_of_mem {X : Subgroup H} {g : H} (hg : g ∈ X) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem hg hy) (X.inv_mem hg)
  · intro hx
    exact ⟨g⁻¹ * x * g, X.mul_mem (X.mul_mem (X.inv_mem hg) hx) hg, by group⟩

theorem centralizer_map_conj (g : H) (S : Subgroup H) :
    Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.centralizer (S : Set H)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, fun y hy => ?_, by group⟩
    have h := hx (g * y * g⁻¹) ⟨y, hy, rfl⟩
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * y := by group
  · rintro ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := hz y hy
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

theorem card_centralizer_map_conj (g : H) (S : Subgroup H) :
    Nat.card ↥(Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)) =
      Nat.card ↥(Subgroup.centralizer (S : Set H)) := by
  rw [centralizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Conj

theorem exists_conj_of_card_six' {X A B : Subgroup H6} (e : Nonempty (↥X ≃* G3))
    (hAX : A ≤ X) (hBX : B ≤ X) (hA : Nat.card A = 6) (hB : Nat.card B = 6) :
    ∃ g ∈ X, (A.map (MulAut.conj g).toMonoidHom) = B := by
  obtain ⟨e⟩ := e
  have hX : IsLnq 3 2 1 X :=
    statedClassicalModel_psl_three_two_of_sl (K := ZMod 2) (by simp) e
  exact exists_conj_of_card_six hX hAX hBX hA hB

theorem genSet_pair (a b : List ℕ × List ℕ) (ha : pairCheck a = true) (hb : pairCheck b = true)
    (h : [a, b].all pairCheck = true) : genSet [a, b] h = {ofCode a ha, ofCode b hb} := by
  ext g
  simp only [genSet, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨cc, hm, rfl⟩
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem all_pair {a b : List ℕ × List ℕ} (ha : pairCheck a = true) (hb : pairCheck b = true) :
    [a, b].all pairCheck = true := by
  simp [ha, hb]

theorem centralizer_pair' {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem card_cen_closure_pair (a b : H6) :
    Nat.card ↥(Subgroup.centralizer ((Subgroup.closure ({a, b} : Set H6) : Subgroup H6) : Set H6))
      = Nat.card ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := by
  rw [Subgroup.centralizer_closure, centralizer_pair']

section Bad


theorem mat6_conj_of_code {g x gi : H6} {cg cx cgi : List ℕ} (hg : mat6 g = dec6 cg)
    (hx : mat6 x = dec6 cx) (hgi : mat6 gi = dec6 cgi) :
    mat6 (g * x * gi) = dec6 (cj cg cx cgi) := by
  rw [map_mul, map_mul, hg, hx, hgi, cj, dec6_mul6, dec6_mul6]

theorem bad_sub {i : Fin 3} {c ci s g gi : List ℕ} (h : badOne i c ci s g gi = true) :
    ∃ S : Subgroup H6, S ≤ Xs i ∧ Nat.card S = 6 ∧
      Nat.card ↥(Subgroup.centralizer (S : Set H6)) = 12 := by
  simp only [badOne, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hs⟩, hg⟩, hcj⟩, hfc⟩, hfs⟩, hcl⟩, hcount⟩ := h
  set C := ofCode (c, ci) hc with hCdef
  set Sg := ofCode (s, s) hs with hSdef
  set Gg := ofCode (g, gi) hg with hGdef
  have mC : mat6 C = dec6 c := mat6_ofCode _ _
  have mS : mat6 Sg = dec6 s := mat6_ofCode _ _
  have mG : mat6 Gg = dec6 g := mat6_ofCode _ _
  have mGi : mat6 Gg⁻¹ = dec6 gi := mat6_ofCode_inv _ _
  have hCX : C ∈ Xs i := mem_Xs_of_found i mC hfc
  have hSX : Sg ∈ Xs i := mem_Xs_of_found i mS hfs
  have hpairs : [(c, ci), (s, s)].all pairCheck = true := all_pair hc hs
  have hgen : genSet [(c, ci), (s, s)] hpairs = {C, Sg} := genSet_pair _ _ hc hs hpairs
  refine ⟨Subgroup.closure {C, Sg}, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hCX
    · rw [Set.mem_singleton_iff.1 hx]
      exact hSX
  · rw [← hgen]
    exact card_closure_genSet _ hpairs 6 hcl
  ·
    have hv : Gg * C * Gg⁻¹ = zH 0 * zH 1 ^ 2 :=
      conj_eq_of_code mG mGi mC mat6_v hcj
    have hs' : mat6 (Gg * Sg * Gg⁻¹) = dec6 (cj g s gi) := mat6_conj_of_code mG mS mGi
    rw [← card_centralizer_map_conj Gg, MonoidHom.map_closure, Set.image_pair]
    have e1 : (MulAut.conj Gg).toMonoidHom C = zH 0 * zH 1 ^ 2 := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hv
    have e2 : (MulAut.conj Gg).toMonoidHom Sg = Gg * Sg * Gg⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e1, e2, card_cen_closure_pair, ← lsAElt_four, ← centSub_eq]
    have hc4 := card_inf_eq_count (centGens 4) (pairs_spec.2.2.2 4) (centOrder 4)
      (cent_spec 4).2.1 (Subgroup.centralizer {Gg * Sg * Gg⁻¹})
      (fun y => commutes6 y (cj g s gi)) (fun x y hx _ => by
        constructor
        · intro hxR
          exact commutes6_of_commute hx hs' (Subgroup.mem_centralizer_singleton_iff.1 hxR)
        · intro hcm
          exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_commutes6 hx hs' hcm))
    exact hc4.trans hcount

end Bad

section NotBad


theorem not_bad {j : Fin 3} (hj : j = 0 ∨ j = 1) (e : Nonempty (↥(Xs j) ≃* G3))
    {S₁ : Subgroup H6} (hS : S₁ ≤ Xs j) (h6 : Nat.card S₁ = 6)
    (h36 : Nat.card ↥(Subgroup.centralizer (S₁ : Set H6)) = 36) : False := by
  have hbad := a2_parts.2.2.1
  simp only [badCheck, Bool.and_eq_true] at hbad
  rcases hj with rfl | rfl
  · obtain ⟨S, hSX, hS6, hSC⟩ := bad_sub hbad.1
    obtain ⟨g, -, hg⟩ := exists_conj_of_card_six' e hS hSX h6 hS6
    rw [← hg, card_centralizer_map_conj, h36] at hSC
    omega
  · obtain ⟨S, hSX, hS6, hSC⟩ := bad_sub hbad.2
    obtain ⟨g, -, hg⟩ := exists_conj_of_card_six' e hS hSX h6 hS6
    rw [← hg, card_centralizer_map_conj, h36] at hSC
    omega

end NotBad

section Good


noncomputable def hH : H6 := ofCode (a2H, a2HI) (by decide +kernel)

theorem mat6_hH : mat6 hH = dec6 a2H := mat6_ofCode _ _

theorem mat6_hH_inv : mat6 hH⁻¹ = dec6 a2HI := mat6_ofCode_inv _ _

noncomputable def Xstar : Subgroup H6 := (Xs 2).map (MulAut.conj hH).toMonoidHom

theorem pairs_K4 : [(a2V, a2V2), (lsSig, lsSig)].all pairCheck = true := by decide +kernel

theorem K4s_eq : K4s = Subgroup.closure (genSet [(a2V, a2V2), (lsSig, lsSig)] pairs_K4) := by
  have h1 : ofCode (a2V, a2V2) (by decide +kernel) = zH 0 * zH 1 ^ 2 := by
    apply mat6_injective
    rw [mat6_ofCode]
    exact mat6_v.symm
  rw [genSet_pair _ _ (by decide +kernel) (by decide +kernel) pairs_K4, h1, K4s]
  rfl

theorem card_K4s : Nat.card K4s = 6 := by
  have h := a2_parts.2.2.2.1
  simp only [goodCheck, Bool.and_eq_true] at h
  rw [K4s_eq]
  exact card_closure_genSet _ pairs_K4 6 h.2

theorem good_sub : ∃ S : Subgroup H6, S ≤ Xs 2 ∧ Nat.card S = 6 ∧
    S.map (MulAut.conj hH).toMonoidHom = K4s := by
  have h := a2_parts.2.2.2.1
  simp only [goodCheck, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hs⟩, hh⟩, hfc⟩, hfs⟩, hcl⟩, hcj⟩, hfk⟩, hk4⟩ := h
  set C := ofCode (a2C2, a2C2I) hc with hCdef
  set Sg := ofCode (a2S2, a2S2) hs with hSdef
  have mC : mat6 C = dec6 a2C2 := mat6_ofCode _ _
  have mS : mat6 Sg = dec6 a2S2 := mat6_ofCode _ _
  have mCi : mat6 C⁻¹ = dec6 a2C2I := mat6_ofCode_inv _ _
  have hCX : C ∈ Xs 2 := mem_Xs_of_found 2 mC hfc
  have hSX : Sg ∈ Xs 2 := mem_Xs_of_found 2 mS hfs
  have hpairs : [(a2C2, a2C2I), (a2S2, a2S2)].all pairCheck = true := all_pair hc hs
  have hgen : genSet [(a2C2, a2C2I), (a2S2, a2S2)] hpairs = {C, Sg} :=
    genSet_pair _ _ hc hs hpairs
  have hhC : hH * C * hH⁻¹ ∈ K4s := by
    rcases hcj with hcj | hcj
    · have : hH * C * hH⁻¹ = zH 0 * zH 1 ^ 2 :=
        conj_eq_of_code mat6_hH mat6_hH_inv mC mat6_v hcj
      rw [this, K4s]
      exact Subgroup.subset_closure (by simp)
    · have : hH * C * hH⁻¹ = zH 0 ^ 2 * zH 1 :=
        conj_eq_of_code mat6_hH mat6_hH_inv mC mat6_vinv hcj
      rw [this, ← inv_v]
      exact K4s.inv_mem (by rw [K4s]; exact Subgroup.subset_closure (by simp))
  have hhS : hH * Sg * hH⁻¹ ∈ K4s := by
    have hm : mat6 (hH * Sg * hH⁻¹) = dec6 (cj a2H a2S2 a2HI) :=
      mat6_conj_of_code mat6_hH mS mat6_hH_inv
    have hmem : cj a2H a2S2 a2HI ∈ closureT ((([(a2V, a2V2), (lsSig, lsSig)] :
        List (List ℕ × List ℕ))).map Prod.fst) := by
      obtain ⟨k, hk, hck⟩ := found_spec hfk
      rw [← hck]
      show _ ∈ closureT a2K4Gens
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
      exact Array.getElem_mem hk
    rw [K4s_eq]
    exact CFSG.Quasithin.H13.U3.mem_closure_of_mem_table _ pairs_K4 6 hk4 hmem hm
  refine ⟨Subgroup.closure {C, Sg}, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hCX
    · rw [Set.mem_singleton_iff.1 hx]
      exact hSX
  · rw [← hgen]
    exact card_closure_genSet _ hpairs 6 hcl
  · have hle : (Subgroup.closure {C, Sg}).map (MulAut.conj hH).toMonoidHom ≤ K4s := by
      rw [MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
      intro x hx
      rcases hx with rfl | hx
      · exact hhC
      · rw [Set.mem_singleton_iff.1 hx]
        exact hhS
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj hH).injective, card_K4s, ← hgen,
      card_closure_genSet _ hpairs 6 hcl]

end Good

section Classify


open CFSG.RankThree.PartTwo.Sec8.Hering418 (z7 orderOf_z7 mat6_z7)

theorem zS_eq : zS = z7 := by
  apply mat6_injective
  rw [mat6_zS, mat6_z7]
  decide +kernel

theorem classify_L32 {Y S : Subgroup H6} (e : Nonempty (↥Y ≃* G3)) (hS : S ≤ Y)
    (hS6 : Nat.card S = 6) (hC : Nat.card ↥(Subgroup.centralizer (S : Set H6)) = 36) :
    ∃ g : H6, Y.map (MulAut.conj g).toMonoidHom = Xstar ∧
      S.map (MulAut.conj g).toMonoidHom = K4s := by
  obtain ⟨e⟩ := e
  have hY : Nat.card Y = 168 := by rw [Nat.card_congr e.toEquiv]; exact card_G3
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 7 (by rw [hY]; norm_num)
  have hx7 : orderOf (x : H6) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g₀, w, hgw, hzw⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.S59.exists_conj_generator (x : H6) hx7
  have hwY : w ∈ Y := by
    have : w ∈ Subgroup.zpowers (x : H6) := hzw ▸ Subgroup.mem_zpowers w
    exact (Subgroup.zpowers_le.2 x.2) this
  set Y₁ := Y.map (MulAut.conj g₀).toMonoidHom with hY₁
  have hz7Y₁ : zS ∈ Y₁ := by
    rw [zS_eq]
    exact ⟨w, hwY, by simpa [MulAut.conj_apply] using hgw⟩
  have hY₁card : Nat.card Y₁ = 168 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hY]
  let e₁ : ↥Y₁ ≃* G3 :=
    (Subgroup.equivMapOfInjective Y (MulAut.conj g₀).toMonoidHom
      (MulAut.conj g₀).injective).symm.trans e
  have hz7ord : orderOf zS = 7 := by rw [zS_eq]; exact orderOf_z7
  have hz7pow : zS ^ 7 = 1 := by rw [← hz7ord]; exact pow_orderOf_eq_one zS
  have hzne : zS ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz7ord
    omega
  set z' : ↥Y₁ := ⟨zS, hz7Y₁⟩ with hz'
  have hx₁7 : (e₁ z') ^ 7 = 1 := by
    rw [← map_pow]
    have : z' ^ 7 = 1 := Subtype.ext (by simpa using hz7pow)
    rw [this, map_one]
  have hx₁1 : e₁ z' ≠ 1 := by
    intro h
    have : z' = 1 := e₁.injective (h.trans (map_one e₁).symm)
    exact hzne (congrArg Subtype.val this)
  obtain ⟨t₁, ht1, ht1ne, ht13⟩ := g3_exists_involution (e₁ z') hx₁7 hx₁1
  set τ₀ : ↥Y₁ := e₁.symm t₁ with hτ₀
  have hτ₀sq : τ₀ * τ₀ = 1 := by rw [← map_mul, ht1, map_one]
  have hτ₀ne : τ₀ ≠ 1 := by
    intro h
    apply ht1ne
    have := congrArg e₁ h
    simpa [hτ₀] using this
  have hτ₀cube : (z' * τ₀) ^ 3 = 1 := by
    apply e₁.injective
    rw [map_pow, map_mul, hτ₀, MulEquiv.apply_symm_apply, ht13, map_one]
  set τ : H6 := (τ₀ : H6) with hτ
  have h2 : τ * τ = 1 := by simpa using congrArg Subtype.val hτ₀sq
  have h1 : τ ≠ 1 := fun h => hτ₀ne (Subtype.ext h)
  have h3 : (zS * τ) ^ 3 = 1 := by simpa [hz'] using congrArg Subtype.val hτ₀cube
  have h4 : zS * τ ≠ 1 := by
    intro h
    have hτ' : τ = zS⁻¹ := eq_inv_of_mul_eq_one_right h
    have hsq : zS ^ 2 = 1 := by
      have h2' := h2
      rw [hτ', ← mul_inv_rev, inv_eq_one] at h2'
      rw [pow_two]
      exact h2'
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hz7ord] at this
    omega
  obtain ⟨hge, hX⟩ := scan_sound h2 h1 h3 h4
  have hQY : Subgroup.closure ({zS, τ} : Set H6) ≤ Y₁ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hz7Y₁
    · rw [Set.mem_singleton_iff.1 hx]
      exact τ₀.2
  have hQcard : Nat.card (Subgroup.closure ({zS, τ} : Set H6)) = 168 :=
    le_antisymm (hY₁card ▸ Subgroup.card_le_of_le hQY) hge
  have hQeq : Subgroup.closure ({zS, τ} : Set H6) = Y₁ :=
    Subgroup.eq_of_le_of_card_ge hQY (by omega)
  obtain ⟨j, hτj⟩ : ∃ j : Fin 3, τ ∈ Xs j := by
    rcases hX hQcard.le with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hQX : Subgroup.closure ({zS, τ} : Set H6) ≤ Xs j := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact zS_mem_Xs j
    · rw [Set.mem_singleton_iff.1 hx]
      exact hτj
  have hQXeq : Subgroup.closure ({zS, τ} : Set H6) = Xs j :=
    Subgroup.eq_of_le_of_card_ge hQX (by rw [card_Xs]; omega)
  have hY₁j : Y₁ = Xs j := hQeq.symm.trans hQXeq
  have hS₁Y₁ : S.map (MulAut.conj g₀).toMonoidHom ≤ Xs j := hY₁j ▸ Subgroup.map_mono hS
  have h6 : Nat.card (S.map (MulAut.conj g₀).toMonoidHom) = 6 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hS6]
  have h36 : Nat.card ↥(Subgroup.centralizer
      ((S.map (MulAut.conj g₀).toMonoidHom : Subgroup H6) : Set H6)) = 36 := by
    rw [card_centralizer_map_conj, hC]
  have ej : Nonempty (↥(Xs j) ≃* G3) := ⟨(MulEquiv.subgroupCongr hY₁j.symm).trans e₁⟩
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl
  · exact (not_bad (Or.inl rfl) ej hS₁Y₁ h6 h36).elim
  · exact (not_bad (Or.inr rfl) ej hS₁Y₁ h6 h36).elim
  · obtain ⟨S₂, hS₂X, hS₂6, hS₂K⟩ := good_sub
    obtain ⟨g₂, hg₂, hg₂S⟩ := exists_conj_of_card_six' ej hS₁Y₁ hS₂X h6 hS₂6
    refine ⟨hH * (g₂ * g₀), ?_, ?_⟩
    · rw [← map_conj_map (g₂ * g₀) hH, ← map_conj_map g₀ g₂, ← hY₁, hY₁j, map_conj_of_mem hg₂]
      rfl
    · rw [← map_conj_map (g₂ * g₀) hH, ← map_conj_map g₀ g₂, hg₂S, hS₂K]

end Classify

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2
