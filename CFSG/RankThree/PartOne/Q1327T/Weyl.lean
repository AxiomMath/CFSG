module

public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartOne.S12.Hyp
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Torsion37

theorem nonempty_range_mulEquiv_of_ker_eq {A B₁ B₂ : Type*} [Group A] [Group B₁] [Group B₂]
    (f₁ : A →* B₁) (f₂ : A →* B₂) (h : f₁.ker = f₂.ker) : Nonempty (f₁.range ≃* f₂.range) :=
  ⟨((QuotientGroup.quotientKerEquivRange f₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans (QuotientGroup.quotientKerEquivRange f₂)⟩

variable {G : Type} [Group G] {p : ℕ}

theorem eq_one_of_mem_zpowers_of_not_mem [Finite G] {a z : G} (hp : p.Prime) (ha : orderOf a = p)
    (hz : z ∈ Subgroup.zpowers a) {S : Subgroup G} (hzS : z ∈ S) (haS : a ∉ S) : z = 1 := by
  by_contra hz1
  have h1 : orderOf z ∣ p := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers a) hz
    rwa [Nat.card_zpowers, ha] at this
  have h2 : orderOf z = p := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have h3 : Subgroup.zpowers z = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, h2])
  apply haS
  have : a ∈ Subgroup.zpowers z := by rw [h3]; exact Subgroup.mem_zpowers a
  exact (Subgroup.zpowers_le.2 hzS) this

theorem inf_le_P [Finite G] {N P E : Subgroup G} {a : G} (hp : p.Prime)
    (haN : ∀ n ∈ N, a * n = n * a) (hao : a ^ p = 1) (ha1 : a ≠ 1) (haNot : a ∉ N) (hPN : P ≤ N)
    (hE : E = Subgroup.zpowers a ⊔ P) : E ⊓ N ≤ P := by
  rintro e ⟨heE, heN⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [hE] at heE
  obtain ⟨s, hs, u, hu, hsu⟩ := exists_mul_of_mem_sup_of_commute
    (K := Subgroup.zpowers a) (L := P) (fun k hk l hl => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact ((Commute.zpow_left (haN l (hPN hl)) m)).eq) heE
  have hsN : s ∈ N := by
    have : s = e * u⁻¹ := by rw [hsu]; group
    rw [this]
    exact N.mul_mem heN (N.inv_mem (hPN hu))
  have hs1 : s = 1 := eq_one_of_mem_zpowers_of_not_mem hp (orderOf_eq_prime hao ha1) hs hsN haNot
  rw [hsu, hs1, one_mul]
  exact hu

theorem mem_torusImage_iff' {E Y : Subgroup G} {φ : MulAut E} :
    φ ∈ torusImage E Y ↔ ∃ (x : G) (_ : x ∈ Y) (hx : x ∈ Subgroup.normalizer (E : Set G)),
      E.normalizerMonoidHom ⟨x, hx⟩ = φ := by
  simp only [torusImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, x.2, rfl⟩
  · rintro ⟨x, hxY, hx, rfl⟩
    exact ⟨⟨x, hx⟩, hxY, rfl⟩

theorem mem_normalizer_of_forward {H : Subgroup G} {w : G} (h1 : ∀ h ∈ H, w * h * w⁻¹ ∈ H)
    (h2 : ∀ h ∈ H, w⁻¹ * h * w⁻¹⁻¹ ∈ H) : w ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

section Weyl

variable {N P E : Subgroup G} {a : G}

theorem mem_normalizer_P [Finite G] (hp : p.Prime) (haN : ∀ n ∈ N, a * n = n * a) (hao : a ^ p = 1)
    (ha1 : a ≠ 1) (haNot : a ∉ N) (hPN : P ≤ N) (hE : E = Subgroup.zpowers a ⊔ P) {w : G}
    (hwN : w ∈ N) (hwE : w ∈ Subgroup.normalizer (E : Set G)) :
    w ∈ Subgroup.normalizer (P : Set G) := by
  have key : ∀ w ∈ N, w ∈ Subgroup.normalizer (E : Set G) → ∀ u ∈ P, w * u * w⁻¹ ∈ P := by
    intro w hw hwE u hu
    have huE : u ∈ E := by rw [hE]; exact Subgroup.mem_sup_right hu
    refine inf_le_P hp haN hao ha1 haNot hPN hE ⟨(Subgroup.mem_normalizer_iff.1 hwE u).1 huE, ?_⟩
    exact N.mul_mem (N.mul_mem hw (hPN hu)) (N.inv_mem hw)
  exact mem_normalizer_of_forward (key w hwN hwE)
    (key w⁻¹ (inv_mem hwN) ((Subgroup.normalizer (E : Set G)).inv_mem hwE))

theorem mem_normalizer_E (haN : ∀ n ∈ N, a * n = n * a) (hPN : P ≤ N)
    (hE : E = Subgroup.zpowers a ⊔ P) {w : G} (hwN : w ∈ N)
    (hwP : w ∈ Subgroup.normalizer (P : Set G)) : w ∈ Subgroup.normalizer (E : Set G) := by
  have key : ∀ w ∈ N, w ∈ Subgroup.normalizer (P : Set G) → ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro w hw hwP e he
    rw [hE] at he
    obtain ⟨s, hs, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (K := Subgroup.zpowers a) (L := P) (fun k hk l hl => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((Commute.zpow_left (haN l (hPN hl)) m)).eq) he
    have hsw : w * s = s * w := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      exact ((Commute.zpow_left (haN w hw) m).symm).eq
    have : w * (s * u) * w⁻¹ = s * (w * u * w⁻¹) := by
      calc w * (s * u) * w⁻¹ = (w * s) * u * w⁻¹ := by group
        _ = (s * w) * u * w⁻¹ := by rw [hsw]
        _ = s * (w * u * w⁻¹) := by group
    rw [this, hE]
    exact Subgroup.mul_mem_sup hs ((Subgroup.mem_normalizer_iff.1 hwP u).1 hu)
  exact mem_normalizer_of_forward (key w hwN hwP)
    (key w⁻¹ (inv_mem hwN) ((Subgroup.normalizer (P : Set G)).inv_mem hwP))

end Weyl

section Main

variable [Finite G] {N P E : Subgroup G} {a : G}

theorem torusImage_equiv (hp : p.Prime) (haN : ∀ n ∈ N, a * n = n * a) (hao : a ^ p = 1)
    (ha1 : a ≠ 1) (haNot : a ∉ N) (hPN : P ≤ N) (hPel : IsElementaryAbelian p ↥P)
    (hE : E = Subgroup.zpowers a ⊔ P) :
    Nonempty (torusImage E N ≃*
      torusImage ((P.subgroupOf N).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥N))) ⊤) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hPel
  set θ := aschbacherSolvableCore p ↥N with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Pn : Subgroup ↥N := P.subgroupOf N with hPn
  have hPnel : IsElementaryAbelian p ↥Pn := IsElementaryAbelian.subgroupOf hPN
  have hPnp : IsPGroup p ↥Pn := IsElementaryAbelian.isPGroup p _
  set Ē : Subgroup (↥N ⧸ θ) := Pn.map π with hĒ
  have hdisj : Pn ⊓ θ = ⊥ := pGroup_inf_theta hp hPnp
  set A : Subgroup ↥N := Subgroup.normalizer (Pn : Set ↥N) with hA
  have hAmem : ∀ w : ↥N, w ∈ A ↔ (w : G) ∈ Subgroup.normalizer (P : Set G) := by
    intro w
    have h := Subgroup.subgroupOf_normalizer_eq hPN
    rw [hA, hPn, ← h]
    exact Iff.rfl
  let βE : ↥A →* ↥(Subgroup.normalizer (E : Set G)) :=
    MonoidHom.codRestrict ((N.subtype).comp (A.subtype)) (Subgroup.normalizer (E : Set G))
      (fun w => mem_normalizer_E haN hPN hE (w.1.2) ((hAmem w.1).1 w.2))
  let αE : ↥A →* MulAut ↥E := E.normalizerMonoidHom.comp βE
  let βQ : ↥A →* ↥(Subgroup.normalizer (Ē : Set (↥N ⧸ θ))) :=
    MonoidHom.codRestrict (π.comp A.subtype) (Subgroup.normalizer (Ē : Set (↥N ⧸ θ)))
      (fun w => Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π w.2))
  let αQ : ↥A →* MulAut ↥Ē := Ē.normalizerMonoidHom.comp βQ
  have hrE : αE.range = torusImage E N := by
    ext g
    rw [mem_torusImage_iff']
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(w.1 : G), w.1.2, (βE w).2, rfl⟩
    · rintro ⟨x, hxN, hxE, rfl⟩
      have hxP : x ∈ Subgroup.normalizer (P : Set G) :=
        mem_normalizer_P hp haN hao ha1 haNot hPN hE hxN hxE
      exact ⟨⟨⟨x, hxN⟩, (hAmem ⟨x, hxN⟩).2 hxP⟩, rfl⟩
  have hrQ : αQ.range = torusImage Ē ⊤ := by
    ext g
    rw [mem_torusImage_iff']
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨π (w : ↥N), Subgroup.mem_top _, (βQ w).2, rfl⟩
    · rintro ⟨y, -, hy, rfl⟩
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨w, hw, e, he, hne⟩ := exists_normalizer_lift hp hPnp (n := n) hy
      refine ⟨⟨w, hw⟩, ?_⟩
      have hĒel : IsElementaryAbelian p ↥Ē := by
        have := hPnel
        exact IsElementaryAbelian.map π
      ext ē
      have hē' : π (w : ↥N) * (ē : ↥N ⧸ θ) * (π (w : ↥N))⁻¹ ∈ Ē :=
        (Subgroup.mem_normalizer_iff.1 (βQ ⟨w, hw⟩).2 ē).1 ē.2
      have hc : e * (π (w : ↥N) * (ē : ↥N ⧸ θ) * (π (w : ↥N))⁻¹) =
          (π (w : ↥N) * (ē : ↥N ⧸ θ) * (π (w : ↥N))⁻¹) * e :=
        congrArg Subtype.val (hĒel.is_comm.comm ⟨e, he⟩ ⟨_, hē'⟩)
      have hconj : (e * π (w : ↥N)) * (ē : ↥N ⧸ θ) * (e * π (w : ↥N))⁻¹ =
          e * (π (w : ↥N) * (ē : ↥N ⧸ θ) * (π (w : ↥N))⁻¹) * e⁻¹ := by group
      show π (w : ↥N) * (ē : ↥N ⧸ θ) * (π (w : ↥N))⁻¹ =
        (n : ↥N ⧸ θ) * (ē : ↥N ⧸ θ) * (n : ↥N ⧸ θ)⁻¹
      rw [hne]
      show _ = (e * π (w : ↥N)) * (ē : ↥N ⧸ θ) * (e * π (w : ↥N))⁻¹
      rw [hconj]
      exact ((mul_inv_eq_iff_eq_mul).2 hc).symm
  have hker : αE.ker = αQ.ker := by
    have hkE : ∀ w : ↥A, w ∈ αE.ker ↔
        ∀ e ∈ E, ((w.1 : ↥N) : G) * e * ((w.1 : ↥N) : G)⁻¹ = e := by
      intro w
      constructor
      · intro h e he
        have h1 := congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) (MonoidHom.mem_ker.1 h)
        simpa [αE, βE, Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
      · intro h
        rw [MonoidHom.mem_ker]
        ext e
        have := h e e.2
        simpa [αE, βE, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    have hkQ : ∀ w : ↥A, w ∈ αQ.ker ↔
        ∀ ē ∈ Ē, π (w.1 : ↥N) * ē * (π (w.1 : ↥N))⁻¹ = ē := by
      intro w
      constructor
      · intro h ē hē
        have h1 := congrArg (fun φ : MulAut ↥Ē => ((φ ⟨ē, hē⟩ : ↥Ē) : ↥N ⧸ θ))
          (MonoidHom.mem_ker.1 h)
        simpa [αQ, βQ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
      · intro h
        rw [MonoidHom.mem_ker]
        ext ē
        have := h ē ē.2
        simpa [αQ, βQ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    ext w
    rw [hkE, hkQ]
    constructor
    · intro h ē hē
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hē
      have hu : ((u' : ↥N) : G) ∈ P := Subgroup.mem_subgroupOf.1 hu'
      have huE : ((u' : ↥N) : G) ∈ E := by rw [hE]; exact Subgroup.mem_sup_right hu
      have h1 := h _ huE
      have h2 : (w.1 : ↥N) * u' * (w.1 : ↥N)⁻¹ = u' := Subtype.ext h1
      rw [← map_mul, ← map_inv, ← map_mul, h2]
    · intro h e he
      rw [hE] at he
      obtain ⟨s, hs, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_commute
        (K := Subgroup.zpowers a) (L := P) (fun k hk l hl => by
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
          exact ((Commute.zpow_left (haN l (hPN hl)) m)).eq) he
      have hsw : ((w.1 : ↥N) : G) * s = s * ((w.1 : ↥N) : G) := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
        exact ((Commute.zpow_left (haN _ (w.1).2) m).symm).eq
      have hu' : (⟨u, hPN hu⟩ : ↥N) ∈ Pn := Subgroup.mem_subgroupOf.2 hu
      have hcomm : π (w.1 : ↥N) * π ⟨u, hPN hu⟩ * (π (w.1 : ↥N))⁻¹ = π ⟨u, hPN hu⟩ :=
        h _ (Subgroup.mem_map_of_mem _ hu')
      have hwn : (w.1 : ↥N) * ⟨u, hPN hu⟩ * (w.1 : ↥N)⁻¹ ∈ Pn := by
        have := (Subgroup.mem_normalizer_iff.1 w.2 ⟨u, hPN hu⟩).1 hu'
        exact this
      have hθ1 : (w.1 : ↥N) * ⟨u, hPN hu⟩ * (w.1 : ↥N)⁻¹ * ⟨u, hPN hu⟩⁻¹ ∈ Pn ⊓ θ := by
        refine ⟨Pn.mul_mem hwn (Pn.inv_mem hu'), (QuotientGroup.eq_one_iff _).1 ?_⟩
        show π ((w.1 : ↥N) * ⟨u, hPN hu⟩ * (w.1 : ↥N)⁻¹ * ⟨u, hPN hu⟩⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
        group
      rw [hdisj, Subgroup.mem_bot] at hθ1
      have hwu : (w.1 : ↥N) * ⟨u, hPN hu⟩ * (w.1 : ↥N)⁻¹ = ⟨u, hPN hu⟩ := by
        have := hθ1
        rw [mul_inv_eq_one] at this
        exact this
      have hwuG : ((w.1 : ↥N) : G) * u * ((w.1 : ↥N) : G)⁻¹ = u := congrArg Subtype.val hwu
      calc ((w.1 : ↥N) : G) * (s * u) * ((w.1 : ↥N) : G)⁻¹
          = (((w.1 : ↥N) : G) * s) * u * ((w.1 : ↥N) : G)⁻¹ := by group
        _ = (s * ((w.1 : ↥N) : G)) * u * ((w.1 : ↥N) : G)⁻¹ := by rw [hsw]
        _ = s * (((w.1 : ↥N) : G) * u * ((w.1 : ↥N) : G)⁻¹) := by group
        _ = s * u := by rw [hwuG]
  obtain ⟨eqv⟩ := nonempty_range_mulEquiv_of_ker_eq αE αQ hker
  exact ⟨(MulEquiv.subgroupCongr hrE).symm.trans (eqv.trans (MulEquiv.subgroupCongr hrQ))⟩

end Main

end CFSG.RankThree.PartOne.Q1327T
