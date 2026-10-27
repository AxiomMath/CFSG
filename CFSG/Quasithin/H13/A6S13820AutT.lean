module

public import CFSG.Quasithin.H13.A6S13820Aut1
public import CFSG.Quasithin.H13.A6S13820AutBorel
public import CFSG.Quasithin.H13.A6S13821z

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Aut20

section Transport

variable {Q R : Type} [Group Q] [Group R]

theorem congr_conj20 (e : Q ≃* R) (g : Q) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem inner_congr_iff20 (e : Q ≃* R) (α : MulAut Q) :
    (∃ g : R, MulAut.congr e α = MulAut.conj g) ↔ ∃ g : Q, α = MulAut.conj g := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.symm g, ?_⟩
    apply (MulAut.congr e).injective
    rw [hg, congr_conj20, MulEquiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨e g, congr_conj20 e g⟩

theorem map_normalizer20 (e : Q ≃* R) (S : Subgroup Q) :
    (Subgroup.normalizer (S : Set Q)).map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup R) : Set R) :=
  Subgroup.map_equiv_normalizer_eq S e

theorem borelAut_mulEquiv20 [Finite Q] [Finite R] (e : Q ≃* R) {S C : Subgroup Q}
    {α : MulAut Q} (h : BorelAut13820 S C α) :
    BorelAut13820 (S.map e.toMonoidHom) (C.map e.toMonoidHom) (MulAut.congr e α) := by
  obtain ⟨hS, hSC, hCN, hCn, hidx, ⟨k, hk⟩, hαS, hcomm⟩ := h
  have hN := map_normalizer20 e S
  refine ⟨?_, Subgroup.map_mono hSC, ?_, ?_, ?_, ⟨k, ?_⟩, ?_, ?_⟩
  · refine ⟨le_top, hS.2.1.map _, ?_⟩
    show ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_map_of_bijective e.bijective]
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.relIndex ⊤ from rfl, Subgroup.relIndex_top_right] at this
  · rw [← hN]
    exact Subgroup.map_mono hCN
  · rw [← hN]
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    obtain ⟨n', hn', hn'e⟩ := n.2
    obtain ⟨c', hc', hc'e⟩ := hc
    have hn'' : (⟨n', hn'⟩ : ↥(Subgroup.normalizer (S : Set Q))) * ⟨c', hCN hc'⟩ *
        (⟨n', hn'⟩ : ↥(Subgroup.normalizer (S : Set Q)))⁻¹ ∈ C.subgroupOf _ :=
      hCn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hc') _
    refine ⟨n' * c' * n'⁻¹, Subgroup.mem_subgroupOf.mp hn'', ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hn'e, hc'e]
  · rw [← hN, Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx
  · rw [← map_pow, hk, map_one]
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨α x, ?_, ?_⟩
      · rw [← hαS]
        exact ⟨x, hx, rfl⟩
      · simp [MulAut.congr_apply]
    · rintro ⟨x, hx, rfl⟩
      rw [← hαS] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      refine ⟨e x', ⟨x', hx', rfl⟩, ?_⟩
      simp [MulAut.congr_apply]
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨c⁻¹ * α c, hcomm c hc, ?_⟩
    simp [MulAut.congr_apply]

end Transport

section CentralQuotient

variable {Q : Type} [Group Q]

@[expose] noncomputable def quotCenterAut20 (Q : Type) [Group Q] :
    MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) where
  toFun σ := QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) σ
    (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem quotCenterAut20_mk (σ : MulAut Q) (y : Q) :
    quotCenterAut20 Q σ (y : Q ⧸ Subgroup.center Q) = ((σ y : Q) : Q ⧸ Subgroup.center Q) := rfl

theorem inner_of_quot20 [Group.IsPerfect Q] {α : MulAut Q} {g : Q ⧸ Subgroup.center Q}
    (h : quotCenterAut20 Q α = MulAut.conj g) : ∃ g : Q, α = MulAut.conj g := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨g', ?_⟩
  have h1 : (MulAut.conj g')⁻¹ * α = 1 := by
    refine eq_one_of_perfect20 fun y => ?_
    have h2 := congrArg (fun φ : MulAut (Q ⧸ Subgroup.center Q) =>
      φ (y : Q ⧸ Subgroup.center Q)) h
    simp only [quotCenterAut20_mk, MulAut.conj_apply] at h2
    have e : (MulAut.conj g')⁻¹ (α y) = g'⁻¹ * α y * g' := by
      rw [← map_inv, MulAut.conj_apply, inv_inv]
    have h3 : ((y⁻¹ * ((MulAut.conj g')⁻¹ * α) y : Q) : Q ⧸ Subgroup.center Q) = 1 := by
      rw [MulAut.mul_apply, e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, h2]
      group
    exact (QuotientGroup.eq_one_iff _).1 h3
  exact (inv_mul_eq_one.mp h1).symm

theorem mem_of_mem_sup_center20 [Finite Q] (hZ : Odd (Nat.card (Subgroup.center Q)))
    {S : Subgroup Q} (hS : IsPGroup 2 S) {y : Q} (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (hy : y ∈ S ⊔ Subgroup.center Q) : y ∈ S := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hy
  obtain ⟨s, hs, z, hz, rfl⟩ := hy
  obtain ⟨a, ha⟩ := hy2
  obtain ⟨b, hb⟩ := hS ⟨s, hs⟩
  have hb' : s ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hzc := Subgroup.mem_center_iff.mp hz
  have hcomm : Commute s z := hzc s
  have hz2 : z ^ 2 ^ (a + b) = 1 := by
    have h1 : (s * z) ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
    have h2 : s ^ 2 ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hb', one_pow]
    rwa [hcomm.mul_pow, h2, one_mul] at h1
  have hzodd : z ^ Nat.card (Subgroup.center Q) = 1 := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center Q))
    rw [orderOf_dvd_iff_pow_eq_one] at h
    have h' := congrArg Subtype.val h
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
  have hz1 : z = 1 := by
    have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card (Subgroup.center Q)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hZ)
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hzodd)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  simpa [hz1] using hs

theorem normalizer_map_center20 [Finite Q] (hZ : Odd (Nat.card (Subgroup.center Q)))
    {S : Subgroup Q} (hS : IsPGroup 2 S) :
    Subgroup.normalizer ((S.map (QuotientGroup.mk' (Subgroup.center Q)) :
        Subgroup (Q ⧸ Subgroup.center Q)) : Set (Q ⧸ Subgroup.center Q)) =
      (Subgroup.normalizer (S : Set Q)).map (QuotientGroup.mk' (Subgroup.center Q)) := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map _)
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
  have key : ∀ g : Q, (QuotientGroup.mk' (Subgroup.center Q) g) ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' (Subgroup.center Q)) : Subgroup (Q ⧸ Subgroup.center Q)) :
        Set (Q ⧸ Subgroup.center Q)) → ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have h1 := (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨s, hs, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    obtain ⟨s', hs', he⟩ := h1
    have h2 : s'⁻¹ * (g * s * g⁻¹) ∈ Subgroup.center Q := by
      have := QuotientGroup.eq.1 he
      simpa using this
    have hmem : g * s * g⁻¹ ∈ S ⊔ Subgroup.center Q := by
      have e : g * s * g⁻¹ = s' * (s'⁻¹ * (g * s * g⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs') (Subgroup.mem_sup_right h2)
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    have hk' : (g * s * g⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow]
      simp [show s ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk]
    exact mem_of_mem_sup_center20 hZ hS ⟨k, hk'⟩ hmem
  refine ⟨y, Subgroup.mem_normalizer_iff.mpr fun s => ⟨key y hx s, fun hs => ?_⟩, rfl⟩
  have hy' : QuotientGroup.mk' (Subgroup.center Q) y⁻¹ ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' (Subgroup.center Q)) : Subgroup (Q ⧸ Subgroup.center Q)) :
        Set (Q ⧸ Subgroup.center Q)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have := key y⁻¹ hy' _ hs
  simpa [mul_assoc] using this

theorem borelAut_quot20 [Finite Q] (hZ : Odd (Nat.card (Subgroup.center Q))) {S C : Subgroup Q}
    {α : MulAut Q} (h : BorelAut13820 S C α) :
    BorelAut13820 (S.map (QuotientGroup.mk' (Subgroup.center Q)))
      (C.map (QuotientGroup.mk' (Subgroup.center Q))) (quotCenterAut20 Q α) := by
  obtain ⟨hS, hSC, hCN, hCn, hidx, ⟨k, hk⟩, hαS, hcomm⟩ := h
  set f := QuotientGroup.mk' (Subgroup.center Q) with hf
  have hN := normalizer_map_center20 hZ hS.2.1
  have hZN : Subgroup.center Q ≤ Subgroup.normalizer (S : Set Q) := fun z hz =>
    Subgroup.mem_normalizer_iff.mpr fun s => by
      rw [(Subgroup.mem_center_iff.mp hz s).symm, mul_inv_cancel_right]
  have hker : f.ker = Subgroup.center Q := QuotientGroup.ker_mk' _
  refine ⟨A6S20.isSylowTwoOf_map_top (QuotientGroup.mk'_surjective _) hS, Subgroup.map_mono hSC,
    ?_, ?_, ?_, ⟨k, ?_⟩, ?_, ?_⟩
  · rw [hN]
    exact Subgroup.map_mono hCN
  · rw [hN]
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    obtain ⟨n', hn', hn'e⟩ := n.2
    obtain ⟨c', hc', hc'e⟩ := hc
    have hn'' : (⟨n', hn'⟩ : ↥(Subgroup.normalizer (S : Set Q))) * ⟨c', hCN hc'⟩ *
        (⟨n', hn'⟩ : ↥(Subgroup.normalizer (S : Set Q)))⁻¹ ∈ C.subgroupOf _ :=
      hCn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hc') _
    refine ⟨n' * c' * n'⁻¹, Subgroup.mem_subgroupOf.mp hn'', ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc'e]
    rw [show f n' = ↑n from hn'e]
  · rw [hN, Subgroup.relIndex_map_map, hker, sup_of_le_left hZN]
    have hCZ : C ≤ C ⊔ Subgroup.center Q := le_sup_left
    have hCZN : C ⊔ Subgroup.center Q ≤ Subgroup.normalizer (S : Set Q) := sup_le hCN hZN
    exact (Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _ hCZ hCZN)).trans hidx
  · rw [← map_pow, hk, map_one]
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨α x, ?_, rfl⟩
      rw [← hαS]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hαS] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨f x', ⟨x', hx', rfl⟩, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨c⁻¹ * α c, hcomm c hc, rfl⟩

end CentralQuotient

end Aut20

end CFSG.Quasithin.H13.A6
