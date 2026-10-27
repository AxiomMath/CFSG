module

public import CFSG.Quasithin.EmptyFaithful.S14610P0
public import CFSG.Quasithin.EmptyFaithful.S152Y22
public import CFSG.Quasithin.Background.F6CatTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem mem_oTwoZIn_iff_commutator {K : Subgroup G} {x : G} :
    x ∈ oTwoZIn K ↔ x ∈ K ∧ ∀ w ∈ K, x * w * x⁻¹ * w⁻¹ ∈ pCoreOf 2 K := by
  rw [S152Y.mem_oTwoZIn_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun w hw => h ⟨w, hw⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun w => h w w.2⟩

omit [Finite G] in
theorem normalizer_le_normalizer_oTwoZIn (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoZIn K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oTwoZIn K, g * x * g⁻¹ ∈ oTwoZIn K := by
    intro g hg x hx
    obtain ⟨hxK, hxc⟩ := mem_oTwoZIn_iff_commutator.mp hx
    have hgc : g ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 K hg
    refine mem_oTwoZIn_iff_commutator.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxK, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg) w).mp hw
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hgc _).mp (hxc _ hw')
    have e : g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ := by group
    rw [e] at h1
    exact h1
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (K : Set G)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem oTwoZIn_le_self (K : Subgroup G) : oTwoZIn K ≤ K := fun _ hx =>
  (mem_oTwoZIn_iff_commutator.mp hx).1

theorem Setting146.oTwoUpper_i1Of1469_le (S : Setting146 G T M) (I : Subgroup G) :
    oTwoUpper (i1Of1469 T M I) ≤ lI T M I := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTL : T ≤ Subgroup.normalizer (yOfL22 T M : Set G) :=
    S.hyp.m_max.1.2.trans S.hyp1281.normal
  have hTI : T ⊓ I ≤ Subgroup.normalizer (lI T M I : Set G) := fun t ht =>
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL ht.1, Subgroup.le_normalizer ht.2⟩)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_of_odd_orderOf_of_sup_pGroup (hT2.to_le inf_le_left) hTI hx.1 hx.2

omit [Finite G] in
theorem false_of_perfect_of_le_sup_solvable {K X K₂ : Subgroup G}
    (hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K)) (hnt : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK₂ : K₂ ≤ K) (hXZ : X ≤ oTwoZIn K) (hKX : K ≤ X ⊔ K₂)
    (hn : K₂ ≤ Subgroup.normalizer (X : Set G)) (hsol : Group.IsSolvable ↥K₂) : False := by
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let C : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)
  let φ : ↥K₂ →* (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ C :=
    (QuotientGroup.mk' C).comp (π.comp (Subgroup.inclusion hK₂))
  have hφ : Function.Surjective φ := by
    intro q'
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : (k : G) ∈ ((K₂ ⊔ X : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hKX k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₂ X hn] at hk
    obtain ⟨y, hy, x, hx, hyx⟩ := hk
    refine ⟨⟨y, hy⟩, ?_⟩
    have hxK : x ∈ K := (oTwoZIn_le_self K) (hXZ hx)
    have hxc : π ⟨x, hxK⟩ ∈ C := by
      have hx' := hXZ hx
      unfold oTwoZIn preimageModTwoCore at hx'
      obtain ⟨x', hx'1, hx'2⟩ := Subgroup.mem_map.mp hx'
      have : x' = ⟨x, hxK⟩ := Subtype.ext hx'2
      subst this
      exact Subgroup.mem_comap.mp hx'1
    have h1 : (QuotientGroup.mk' C) (π ⟨x, hxK⟩) = 1 := (QuotientGroup.eq_one_iff _).mpr hxc
    have e : π k = π (Subgroup.inclusion hK₂ ⟨y, hy⟩) * π ⟨x, hxK⟩ := by
      rw [← map_mul]
      exact congrArg π (Subtype.ext hyx.symm)
    show (QuotientGroup.mk' C) (π (Subgroup.inclusion hK₂ ⟨y, hy⟩)) = (QuotientGroup.mk' C) (π k)
    rw [e, map_mul, h1, mul_one]
  have := hperf
  have := hnt
  have : Group.IsSolvable ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ C) := Group.isSolvable_of_surjective hφ
  have : Group.IsSolvable ↥C :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1)
  have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.isSolvable_of_ker_le_range C.subtype (QuotientGroup.mk' C)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact Group.IsPerfect.not_isSolvable (↥K ⧸ CFSG.pCore 2 ↥K) inferInstance

theorem Setting146.facts14610_hat6 (i13 : Input14610Hat6) {H : Subgroup G} {u : G}
    {I I₂ K : Subgroup G} (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K)
    (hHat : IsHatA6Block K) : False := by
  have S : Setting146 G T M := c.setting
  have hXI : oTwoUpper (oTwoZIn K) ≤ I :=
    ((oTwoUpper_le _).trans (oTwoZIn_le_self K)).trans hK.le
  have hIN : I ≤ Subgroup.normalizer (oTwoUpper (oTwoZIn K) : Set G) :=
    hK.normal.trans ((normalizer_le_normalizer_oTwoZIn K).trans
      (normalizer_le_normalizer_oTwoUpper _))
  rcases c.c3 _ hXI ((i1Of1469_le T M I).trans hIN) with h | h
  · have hK1 : oTwoUpper (i1Of1469 T M I) ≤ oTwoUpper (oTwoZIn K) :=
      (S.oTwoUpper_i1Of1469_le I).trans h
    have hK₂K : oTwoUpper I₂ ≤ K := le_sup_right.trans hK.gen.ge
    have hKX : K ≤ oTwoUpper (oTwoZIn K) ⊔ oTwoUpper I₂ :=
      hK.gen.le.trans (sup_le_sup_right hK1 _)
    have hsolI₂ : Group.IsSolvable ↥I₂ := F6.isSolvable_of_quotient_pCore c.s3.some
    have : Group.IsSolvable ↥(oTwoUpper I₂) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (oTwoUpper_le I₂))
    obtain ⟨-, hhat, -⟩ := hHat
    obtain ⟨hqs, hcen, -⟩ := hhat
    have hnt : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := by
      have h3 : 1 < Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by omega
      have : Nontrivial ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := Finite.one_lt_card_iff_nontrivial.mp h3
      obtain ⟨a, ha⟩ := exists_ne (1 : ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
      exact ⟨⟨a.1, 1, fun h => ha (Subtype.ext h)⟩⟩
    exact false_of_perfect_of_le_sup_solvable hqs.1 hnt hK₂K ((oTwoUpper_le _)) hKX
      (hK₂K.trans (hK.le.trans hIN)) inferInstance
  · have hVC : VZ T M ≤ Subgroup.centralizer ((oTwoUpper (oTwoZIn K) : Subgroup G) : Set G) :=
      fun v hv x hx => (Subgroup.mem_centralizer_iff.mp (h hx).2 v hv).symm
    have hV : VZ T M ≤
        wOf1469 K ⊓ Subgroup.centralizer ((oTwoUpper (oTwoZIn K) : Subgroup G) : Set G) :=
      le_inf hK.v_le_w hVC
    rw [i13 G K hHat] at hV
    have h4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
    rw [le_bot_iff.mp hV, Subgroup.card_bot] at h4
    omega

end CFSG.Quasithin
