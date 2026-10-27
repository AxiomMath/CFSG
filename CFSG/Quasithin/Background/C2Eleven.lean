module

public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H R M L V T : Subgroup G}

namespace C2Eleven

omit [Finite G] in
theorem conjByElt_one (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

omit [Finite G] in
theorem conjByElt_mul (a b : G) (K : Subgroup G) :
    conjByElt (a * b) K = conjByElt a (conjByElt b K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

omit [Finite G] in
theorem mem_normalizer_iff_conjByElt {K : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (K : Set G) ↔ conjByElt g K = K :=
  Subgroup.mem_normalizer_iff_map_conj_eq

omit [Finite G] in
theorem conj_mem_conjByElt {K : Subgroup G} {g x : G} (hx : x ∈ K) :
    g * x * g⁻¹ ∈ conjByElt g K := by
  rw [mem_conjByElt]
  simpa [mul_assoc] using hx

omit [Finite G] in
theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

omit [Finite G] in
theorem not_mem_centerOf_conjByElt {K : Subgroup G} {g x : G} (hx : x ∉ centerOf K) :
    g * x * g⁻¹ ∉ centerOf (conjByElt g K) := by
  intro h
  apply hx
  unfold centerOf at h ⊢
  obtain ⟨hmem, hcent⟩ := Subgroup.mem_inf.mp h
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_conjByElt] at hmem
    simpa [mul_assoc] using hmem
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := Subgroup.mem_centralizer_iff.mp hcent (g * k * g⁻¹) (conj_mem_conjByElt hk)
    have h2 : g * (k * x) * g⁻¹ = g * (x * k) * g⁻¹ := by
      calc g * (k * x) * g⁻¹ = g * k * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * k * g⁻¹) := h1
        _ = g * (x * k) * g⁻¹ := by group
    simpa using h2

theorem elemAbelian_step {p : ℕ} (hp : p.Prime) {E L K : Subgroup G} (hE : IsElemAbelian p E)
    (hEL : E ≤ L) (hLK : L ≤ Subgroup.centralizer (K : Set G)) {y : G} (hyK : y ∈ K)
    (hy : orderOf y = p) (hyc : y ∉ centerOf K) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers y) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers y) = Nat.card E * p := by
  have : Fact p.Prime := ⟨hp⟩
  refine exists_elemAbelian_sup_zpowers hE hy (fun e he => ?_) (fun hyE => hyc ⟨hyK, ?_⟩)
  · exact (Subgroup.mem_centralizer_iff.mp (hLK (hEL he)) y hyK).symm
  · exact hLK (hEL hyE)

theorem three_le_pRank {p : ℕ} (hp : p.Prime) {K₁ K₂ K₃ H : Subgroup G} {x₁ x₂ x₃ : G}
    (h12 : ⁅K₁, K₂⁆ = ⊥) (h13 : ⁅K₁, K₃⁆ = ⊥) (h23 : ⁅K₂, K₃⁆ = ⊥)
    (hK₁ : K₁ ≤ H) (hK₂ : K₂ ≤ H) (hK₃ : K₃ ≤ H)
    (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hx₃ : x₃ ∈ K₃)
    (ho₁ : orderOf x₁ = p) (ho₂ : orderOf x₂ = p) (ho₃ : orderOf x₃ = p)
    (hc₁ : x₁ ∉ centerOf K₁) (hc₂ : x₂ ∉ centerOf K₂) (hc₃ : x₃ ∉ centerOf K₃) :
    3 ≤ CFSG.Open.pRank p H := by
  have c12 : K₁ ≤ Subgroup.centralizer (K₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h12
  have c13 : K₁ ≤ Subgroup.centralizer (K₃ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h13
  have c23 : K₂ ≤ Subgroup.centralizer (K₃ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h23
  have c123 : K₁ ⊔ K₂ ≤ Subgroup.centralizer (K₃ : Set G) := sup_le c13 c23
  have hE0 : IsElemAbelian p (⊥ : Subgroup G) := CFSG.SectionRank.isElemAbelian_bot p
  obtain ⟨hE1, hc1⟩ := elemAbelian_step hp hE0 (L := ⊥) le_rfl bot_le hx₁ ho₁ hc₁
  have hE1K : (⊥ : Subgroup G) ⊔ Subgroup.zpowers x₁ ≤ K₁ :=
    sup_le bot_le (Subgroup.zpowers_le.mpr hx₁)
  obtain ⟨hE2, hc2⟩ := elemAbelian_step hp hE1 hE1K c12 hx₂ ho₂ hc₂
  have hE2K : (⊥ ⊔ Subgroup.zpowers x₁) ⊔ Subgroup.zpowers x₂ ≤ K₁ ⊔ K₂ :=
    sup_le (hE1K.trans le_sup_left) ((Subgroup.zpowers_le.mpr hx₂).trans le_sup_right)
  obtain ⟨hE3, hc3⟩ := elemAbelian_step hp hE2 hE2K c123 hx₃ ho₃ hc₃
  have hE3H : ((⊥ ⊔ Subgroup.zpowers x₁) ⊔ Subgroup.zpowers x₂) ⊔ Subgroup.zpowers x₃ ≤ H :=
    sup_le (hE2K.trans (sup_le hK₁ hK₂)) ((Subgroup.zpowers_le.mpr hx₃).trans hK₃)
  refine CFSG.Quasithin.le_pRank hp hE3H hE3 (k := 3) ?_
  rw [hc3, hc2, hc1, Subgroup.card_bot]
  ring

theorem conjByElt_eq_or_eq_or_eq (hC19 : ASC19Statement G) (hH : IsSQTKIn H)
    (hO : oddCoreIn H = ⊥) {B : Subgroup G} (hB : IsBlock2 H B) {x : G} (hxB : x ∈ B)
    (hxo : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) (hxc : x ∉ centerOf B)
    {g₁ g₂ g₃ : G} (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H) (h₃ : g₃ ∈ H) :
    conjByElt g₁ B = conjByElt g₂ B ∨ conjByElt g₁ B = conjByElt g₃ B ∨
      conjByElt g₂ B = conjByElt g₃ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n23⟩ := hcon
  have hcomm : ∀ {a b : G}, a ∈ H → b ∈ H → conjByElt a B ≠ conjByElt b B →
      ⁅conjByElt a B, conjByElt b B⁆ = ⊥ := fun ha hb hne =>
    hC19 H _ _ (fun _ => charTwo_oTwoThreeIn_of_oddCore_eq_bot hO)
      (IsBlock2.conjByElt_of_mem hB ha) (IsBlock2.conjByElt_of_mem hB hb) hne
  have hle : ∀ {a : G}, a ∈ H → conjByElt a B ≤ H := fun ha =>
    (IsBlock2.conjByElt_of_mem hB ha).2.1
  have hrank : CFSG.Open.pRank (orderOf x) H ≤ 2 := by
    have : Fact (orderOf x).Prime := ⟨hxo⟩
    have h1 := sqt_iff.mp hH.1 (orderOf x) hxo hx2
    rw [pRank_top_subtype] at h1
    exact h1
  have h3 := three_le_pRank hxo (hcomm h₁ h₂ n12) (hcomm h₁ h₃ n13) (hcomm h₂ h₃ n23)
    (hle h₁) (hle h₂) (hle h₃) (conj_mem_conjByElt hxB) (conj_mem_conjByElt hxB)
    (conj_mem_conjByElt hxB) (orderOf_conj_eq g₁ x) (orderOf_conj_eq g₂ x)
    (orderOf_conj_eq g₃ x) (not_mem_centerOf_conjByElt hxc) (not_mem_centerOf_conjByElt hxc)
    (not_mem_centerOf_conjByElt hxc)
  omega

theorem eq_top_of_perfect_of_card_quotient_le_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (N : Subgroup Q) (hN : Nat.card (Q ⧸ N) ≤ 2) : N = ⊤ := by
  have hsolv : Group.IsSolvable (Equiv.Perm (Q ⧸ N)) := Equiv.Perm.isSolvable (by omega)
  let φ : Q →* Equiv.Perm (Q ⧸ N) := MulAction.toPermHom Q (Q ⧸ N)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance
  refine eq_top_iff.mpr fun q _ => ?_
  have h1 : φ q = 1 := by
    have : φ q ∈ φ.range := ⟨q, rfl⟩
    rw [hr] at this
    exact this
  have h2 : q • (QuotientGroup.mk 1 : Q ⧸ N) = QuotientGroup.mk 1 := by
    have := congrArg (fun f : Equiv.Perm (Q ⧸ N) => f (QuotientGroup.mk 1)) h1
    simpa [φ] using this
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h2
  simpa using N.inv_mem h2

omit [Finite G] in
theorem isBlock2_of_isBlock2_oTwoFIn {X : Subgroup G} (hX : IsBlock2 (oTwoFIn H) X) :
    IsBlock2 H X := by
  have hXH : X ≤ H := hX.2.1.trans C2Six.oTwoFIn_le
  refine ⟨hX.1, hXH, ?_⟩
  have h2 : IsSubnormal (oTwoFIn H) H :=
    A3.subnormal_of_normal C2Six.oTwoFIn_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer C2Six.oTwoFIn_le).mpr
        C2Six.le_normalizer_oTwoFIn)
  exact (isSubnormal_iff_subgroupOf hXH).mp
    (A3.subnormal_trans (IsBlock2.isSubnormal hX) h2)

end C2Eleven

theorem perfect_le_normalizer_of_odd_prime (hC19 : ASC19Statement G) (hH : IsSQTKIn H)
    (hO : oddCoreIn H = ⊥) {P B : Subgroup G} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P)
    (hB : IsBlock2 H B) {x : G} (hxB : x ∈ B) (hxo : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxc : x ∉ centerOf B) : P ≤ Subgroup.normalizer (B : Set G) := by
  let N : Subgroup ↥P := (Subgroup.normalizer (B : Set G)).comap P.subtype
  have hP' : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hmem : ∀ a : ↥P, a ∈ N ↔ conjByElt (a : G) B = B := fun a =>
    C2Eleven.mem_normalizer_iff_conjByElt
  have key : ∀ a b : ↥P, conjByElt (a : G) B = conjByElt (b : G) B →
      (QuotientGroup.mk a : ↥P ⧸ N) = QuotientGroup.mk b := by
    intro a b hab
    rw [QuotientGroup.eq, hmem, Subgroup.coe_mul, Subgroup.coe_inv, C2Eleven.conjByElt_mul, ← hab,
      ← C2Eleven.conjByElt_mul, inv_mul_cancel, C2Eleven.conjByElt_one]
  have hcard : Nat.card (↥P ⧸ N) ≤ 2 := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have := Fintype.ofFinite (↥P ⧸ N)
    rw [Nat.card_eq_fintype_card] at hlt
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hlt
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
    rcases C2Eleven.conjByElt_eq_or_eq_or_eq hC19 hH hO hB hxB hxo hx2 hxc (hPH a.2) (hPH b.2)
      (hPH c.2) with h | h | h
    · exact hab (key a b h)
    · exact hac (key a c h)
    · exact hbc (key b c h)
  have hN : N = ⊤ := C2Eleven.eq_top_of_perfect_of_card_quotient_le_two hP' N hcard
  intro g hg
  have : (⟨g, hg⟩ : ↥P) ∈ N := by rw [hN]; exact Subgroup.mem_top _
  exact this

theorem c2_11 (hC129 : ASC129Statement G) (hC19 : ASC19Statement G) (h : HypC28 H R M L V) :
    oTwoFIn H ≤ M := by
  by_contra hnot
  have hO : oddCoreIn H = ⊥ := c2_10_one h
  obtain ⟨r, Lb, hLb, hprod⟩ :=
    c2_6_two hC129 (c2_10_four h) (charTwo_oTwoFIn_of_oddCore_eq_bot hO) hnot
  have hr : 0 < r := by
    by_contra hr0
    obtain rfl : r = 0 := Nat.eq_zero_of_not_pos hr0
    apply hnot
    intro x hx
    obtain ⟨m, hm, y, -, rfl⟩ := hprod x hx
    simpa using hm.1
  obtain ⟨hXb, hX3, hXM⟩ := hLb ⟨0, hr⟩
  set X : Subgroup G := Lb ⟨0, hr⟩ with hXdef
  have hXH : IsBlock2 H X := C2Eleven.isBlock2_of_isBlock2_oTwoFIn hXb
  obtain ⟨c, hcX, hcp, hc2, hcc⟩ :=
    exists_noncentral_odd_prime_of_isChi0Block (X := oTwoFIn H) (B := X)
      ⟨hXb, Or.inr (Or.inl hX3)⟩
  have hM0H : conjClosure L M ≤ H := (C2Nine.conjClosure_le_M h).trans h.le_H
  have hperf := C2Nine.perfect_conjClosure_of_hyp h
  have hnorm : conjClosure L M ≤ Subgroup.normalizer (X : Set G) :=
    perfect_le_normalizer_of_odd_prime hC19 h.sqtk hO hM0H hperf hXH hcX hcp hc2 hcc
  have hcent : conjClosure L M ≤ Subgroup.centralizer (X : Set G) :=
    perfect_le_centralizer_of_isAltType_three hXH.1 hX3 hnorm hperf
  have hXV : X ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hcent (h.V_le hv)) x hx).symm
  exact hXM fun x hx => h.V_norm ⟨hXH.2.1 hx, Subgroup.centralizer_le_normalizer _ (hXV hx)⟩

end CFSG.Quasithin
