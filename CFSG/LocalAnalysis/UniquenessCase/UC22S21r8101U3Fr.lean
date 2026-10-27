module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UMat
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101U3Bar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UFr
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

structure U81BasisR (D : Data G) (L K : Subgroup G) (r : ℕ) (B : Subgroup G) (b : Fin 3 → G) :
    Prop where
  frame : U81Frame r B b
  mem_L : b 0 ∈ L
  mem_K : b 1 ∈ K
  bar_C : ∀ h : b 2 ∈ D.M, uc22p21cPi D.M ⟨b 2, h⟩ ∈ centralizer
    ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))
  inf_L : B ⊓ L ≤ zpowers (b 0)
  inf_K : B ⊓ K ≤ zpowers (b 1)
  inf_C : ∀ m : ↥D.M, (m : G) ∈ B → uc22p21cPi D.M m ∈ centralizer
    ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) →
      (m : G) ∈ zpowers (b 2)

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem u81_exists_basis (u : U4P D L K n p) {r : ℕ} (hr : r.Prime) (hrp : r ∣ 2 ^ p - 1)
    (hr3 : CFSG.Open.pRank r D.M ≤ 3) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (hBR : B ≤ R) (hBel : IsElemAbelian r B)
    (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ B)
    (hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥) :
    ∃ b : Fin 3 → G, U81BasisR D L K r B b := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hBM : B ≤ D.M := hBR.trans hR.le
  have hBp : IsPGroup r B := hR.isPGroup.to_le hBR
  obtain ⟨-, hinf, -, -, -, -, hXC⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hb01 : ∀ {Y Y' : Subgroup G}, U4P D Y Y' n p → ∃ a ∈ B ⊓ Y, orderOf a = r := by
    intro Y Y' v
    obtain ⟨a, ha, hao⟩ := v.u81_exists_mem_inf hr hrp hR
    exact ⟨a, Subgroup.mem_inf.2 ⟨hΩ a ha.1 (by rw [← hao]; exact pow_orderOf_eq_one a), ha.2⟩, hao⟩
  obtain ⟨a₀, ha₀, ha₀o⟩ := hb01 u
  obtain ⟨a₁, ha₁, ha₁o⟩ := hb01 u.symm
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB0
  obtain ⟨m₂, hm₂B, rfl⟩ := uc22p21c_mem_barImage.1 hc.1
  set m₀ : ↥D.M := ⟨a₀, hBM ha₀.1⟩
  set m₁ : ↥D.M := ⟨a₁, hBM ha₁.1⟩
  set b : Fin 3 → G := ![a₀, a₁, (m₂ : G)] with hbdef
  have hbB : ∀ i, b i ∈ B := by
    intro i
    fin_cases i
    exacts [ha₀.1, ha₁.1, hm₂B]
  have hx0 : uc22p21cPi D.M m₀ ∈ barImage D.M L := uc22p21c_mem_barImage.2 ⟨m₀, ha₀.2, rfl⟩
  have hx1 : uc22p21cPi D.M m₁ ∈ barImage D.M K := uc22p21c_mem_barImage.2 ⟨m₁, ha₁.2, rfl⟩
  have hx2 := hc.2
  have hpow : ∀ m : ↥D.M, (m : G) ∈ B → uc22p21cPi D.M m ^ r = 1 := fun m hm => by
    rw [← map_pow, show m ^ r = 1 from Subtype.ext (hBel.2 _ hm), map_one]
  have hne : ∀ m : ↥D.M, (m : G) ∈ B → orderOf (m : G) = r → uc22p21cPi D.M m ≠ 1 := by
    intro m hm ho h1
    have h := u81_eq_of_pi_eq hr (u.r_ne_two hr hrp) hBp hm B.one_mem (h1.trans (map_one _).symm)
    rw [h, Subgroup.coe_one, orderOf_one] at ho
    exact hr.one_lt.ne ho
  have ho0 : orderOf (uc22p21cPi D.M m₀) = r :=
    orderOf_eq_prime (hpow m₀ ha₀.1) (hne m₀ ha₀.1 ha₀o)
  have ho1 : orderOf (uc22p21cPi D.M m₁) = r :=
    orderOf_eq_prime (hpow m₁ ha₁.1) (hne m₁ ha₁.1 ha₁o)
  have ho2 : orderOf (uc22p21cPi D.M m₂) = r :=
    orderOf_eq_prime (hpow m₂ hm₂B) fun h => hc1 (Subtype.ext h)
  have hexp : ∀ {x : Bar2 D.M}, orderOf x = r →
      ∀ k k' : ZMod r, x ^ k.val = x ^ k'.val → k = k' := by
    intro x hx k k' h
    rw [pow_inj_mod, hx, Nat.mod_eq_of_lt (ZMod.val_lt k), Nat.mod_eq_of_lt (ZMod.val_lt k')] at h
    exact ZMod.val_injective _ h
  have hzero : ∀ {x : Bar2 D.M}, orderOf x = r → ∀ k : ZMod r, x ^ k.val = 1 → k = 0 :=
    fun hx k h => hexp hx k 0 (by rw [h, ZMod.val_zero, pow_zero])
  set mc : (Fin 3 → ZMod r) → ↥D.M := fun a =>
    m₀ ^ (a 0).val * m₁ ^ (a 1).val * m₂ ^ (a 2).val with hmcdef
  have hmc : ∀ a : Fin 3 → ZMod r, ((mc a : ↥D.M) : G) = u81Coord b a := fun a => by
    simp only [mc, u81Coord, Subgroup.coe_mul, Subgroup.coe_pow]
    rfl
  have hπmc : ∀ a : Fin 3 → ZMod r, uc22p21cPi D.M (mc a) = uc22p21cPi D.M m₀ ^ (a 0).val *
      uc22p21cPi D.M m₁ ^ (a 1).val * uc22p21cPi D.M m₂ ^ (a 2).val := fun a => by
    simp only [mc, map_mul, map_pow]
  have hdec : ∀ (a : Fin 3 → ZMod r) {x y z : Bar2 D.M}, x ∈ barImage D.M L →
      y ∈ barImage D.M K →
      z ∈ centralizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) →
      uc22p21cPi D.M (mc a) = x * y * z →
      uc22p21cPi D.M m₀ ^ (a 0).val = x ∧ uc22p21cPi D.M m₁ ^ (a 1).val = y ∧
        uc22p21cPi D.M m₂ ^ (a 2).val = z := fun a x y z hx hy hz h =>
    u81_eq_of_mul_mul_eq hinf hXC (pow_mem hx0 _) hx (pow_mem hx1 _) hy (pow_mem hx2 _) hz
      ((hπmc a).symm.trans h)
  have hinj : ∀ a a' : Fin 3 → ZMod r, u81Coord b a = u81Coord b a' → a = a' := by
    intro a a' h
    have h' : uc22p21cPi D.M (mc a) = uc22p21cPi D.M (mc a') := by
      rw [show mc a = mc a' from Subtype.ext ((hmc a).trans (h.trans (hmc a').symm))]
    rw [hπmc a'] at h'
    obtain ⟨e0, e1, e2⟩ := hdec a (pow_mem hx0 _) (pow_mem hx1 _) (pow_mem hx2 _) h'
    funext i
    fin_cases i
    exacts [hexp ho0 _ _ e0, hexp ho1 _ _ e1, hexp ho2 _ _ e2]
  have hcm : ∀ a : Fin 3 → ZMod r, u81Coord b a ∈ B := fun a =>
    B.mul_mem (B.mul_mem (B.pow_mem (hbB 0) _) (B.pow_mem (hbB 1) _)) (B.pow_mem (hbB 2) _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hBp
  have hcard : Nat.card ↥B ≤ Nat.card (Fin 3 → ZMod r) := by
    rw [hk, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    exact Nat.pow_le_pow_right hr.pos ((UC6S846.le_pRank' hr hBM hBel hk).trans hr3)
  have hφ : Function.Injective fun a : Fin 3 → ZMod r => (⟨u81Coord b a, hcm a⟩ : ↥B) :=
    fun a a' h => hinj a a' (congrArg Subtype.val h)
  have hbij := hφ.bijective_of_nat_card_le hcard
  have hspan : ∀ x ∈ B, ∃ a : Fin 3 → ZMod r, u81Coord b a = x := fun x hx =>
    (hbij.2 ⟨x, hx⟩).imp fun _ h => congrArg Subtype.val h
  have hF : U81Frame r B b :=
    ⟨hBel, hbB, fun a h => hinj a 0 (h.trans (u81Coord_zero b).symm), hspan⟩
  have hmcL : ∀ {x : G} {a : Fin 3 → ZMod r}, u81Coord b a = x → ∀ (Y : Subgroup G), x ∈ Y →
      uc22p21cPi D.M (mc a) ∈ barImage D.M Y := fun {x a} ha Y hx =>
    uc22p21c_mem_barImage.2 ⟨mc a, by rw [hmc a, ha]; exact hx, rfl⟩
  refine ⟨b, hF, ha₀.2, ha₁.2, fun _ => hx2, ?_, ?_, ?_⟩
  · rintro x ⟨hxB, hxL⟩
    obtain ⟨a, rfl⟩ := hspan x hxB
    obtain ⟨-, e1, e2⟩ :=
      hdec a (hmcL rfl L hxL) (one_mem _) (one_mem _) (by rw [mul_one, mul_one])
    have h1 := hzero ho1 _ e1
    have h2 := hzero ho2 _ e2
    simp only [u81Coord, h1, h2, ZMod.val_zero, pow_zero, mul_one]
    exact pow_mem (mem_zpowers _) _
  · rintro x ⟨hxB, hxK⟩
    obtain ⟨a, rfl⟩ := hspan x hxB
    obtain ⟨e0, -, e2⟩ :=
      hdec a (one_mem _) (hmcL rfl K hxK) (one_mem _) (by rw [one_mul, mul_one])
    have h0 := hzero ho0 _ e0
    have h2 := hzero ho2 _ e2
    simp only [u81Coord, h0, h2, ZMod.val_zero, pow_zero, one_mul, mul_one]
    exact pow_mem (mem_zpowers _) _
  · intro m hmB hmC
    obtain ⟨a, ha⟩ := hspan _ hmB
    have hma : mc a = m := Subtype.ext ((hmc a).trans ha)
    obtain ⟨e0, e1, -⟩ := hdec a (one_mem _) (one_mem _) hmC (by rw [hma, one_mul, one_mul])
    have h0 := hzero ho0 _ e0
    have h1 := hzero ho1 _ e1
    rw [← ha]
    simp only [u81Coord, h0, h1, ZMod.val_zero, pow_zero, one_mul]
    exact pow_mem (mem_zpowers _) _

end U4P

namespace U81BasisR

variable {D : Data G} {L K B : Subgroup G} {r : ℕ} {b : Fin 3 → G}

theorem orderOf_eq (hb : U81BasisR D L K r B b) (hr : r.Prime) (i : Fin 3) : orderOf (b i) = r := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : Fact (1 < r) := ⟨hr.one_lt⟩
  rcases hr.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hb.frame.pow_eq_one i)) with h | h
  · rw [orderOf_eq_one_iff] at h
    have h0 := congrFun (hb.frame.indep (Pi.single i 1) (by rw [hb.frame.coord_single_one, h])) i
    rw [Pi.single_eq_same, Pi.zero_apply] at h0
    exact absurd h0 one_ne_zero
  · exact h

theorem conj_mem_zpowers {n p : ℕ} (hb : U81BasisR D L K r B b) (u : U4P D L K n p)
    (hBM : B ≤ D.M) {x : G} (hxM : x ∈ D.M) (hxB : x ∈ normalizer (B : Set G))
    (hodd : Odd (orderOf x)) (i : Fin 3) : x * b i * x⁻¹ ∈ zpowers (b i) := by
  have hxL := uc22p2214_mem_normalizer_of_odd u.hc2 hxM hodd
  have hxK := uc22p2214_mem_normalizer_of_odd u.symm.hc2 hxM hodd
  have hBc : ∀ j, x * b j * x⁻¹ ∈ B := fun j => (mem_normalizer_iff.1 hxB _).1 (hb.frame.mem j)
  fin_cases i
  · exact hb.inf_L (Subgroup.mem_inf.2 ⟨hBc 0, (mem_normalizer_iff.1 hxL _).1 hb.mem_L⟩)
  · exact hb.inf_K (Subgroup.mem_inf.2 ⟨hBc 1, (mem_normalizer_iff.1 hxK _).1 hb.mem_K⟩)
  · have h2M : b 2 ∈ D.M := hBM (hb.frame.mem 2)
    have hcM : x * b 2 * x⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hxM h2M) (D.M.inv_mem hxM)
    set g : Bar2 D.M := uc22p21cPi D.M ⟨x, hxM⟩ with hg
    have hgN : g ∈ normalizer ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) :
        Set (Bar2 D.M)) :=
      Subgroup.inf_normalizer_le_normalizer_sup _ _
        (Subgroup.mem_inf.2 ⟨uc22ine229_mk_mem_normalizer hxL, uc22ine229_mk_mem_normalizer hxK⟩)
    refine hb.inf_C ⟨x * b 2 * x⁻¹, hcM⟩ (hBc 2) ?_
    have he : uc22p21cPi D.M ⟨x * b 2 * x⁻¹, hcM⟩ = g * uc22p21cPi D.M ⟨b 2, h2M⟩ * g⁻¹ := by
      rw [hg, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [he, mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ barImage D.M L ⊔ barImage D.M K := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) s).1 hs
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 (hb.bar_C h2M) _ hs'
    calc s * (g * uc22p21cPi D.M ⟨b 2, h2M⟩ * g⁻¹)
        = g * ((g⁻¹ * s * g) * uc22p21cPi D.M ⟨b 2, h2M⟩) * g⁻¹ := by group
      _ = g * (uc22p21cPi D.M ⟨b 2, h2M⟩ * (g⁻¹ * s * g)) * g⁻¹ := by rw [hc]
      _ = g * uc22p21cPi D.M ⟨b 2, h2M⟩ * g⁻¹ * s := by group

end U81BasisR

end CFSG.LocalAnalysis.UniquenessCase.UC22
