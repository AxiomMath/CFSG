module

public import CFSG.Milestones.ASVolI.A3L3.Defs
public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

open scoped Pointwise

@[expose] noncomputable def burnsideA315y_alpha {G P : Type} [Group G] [Group P] (L : Subgroup G)
    [L.Normal] (e : ↥L ≃* P) : G →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem burnsideA315y_alpha_apply {G P : Type} [Group G] [Group P] (L : Subgroup G) [L.Normal]
    (e : ↥L ≃* P) (g : G) (y : P) :
    burnsideA315y_alpha L e g y = e (MulAut.conjNormal g (e.symm y)) :=
  rfl

theorem burnsideA315y_alpha_injective {G P : Type} [Group G] [Group P] (L : Subgroup G) [L.Normal]
    (e : ↥L ≃* P) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    Function.Injective (burnsideA315y_alpha L e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : burnsideA315y_alpha L e g (e ⟨l, hl⟩) = e ⟨l, hl⟩ := by
      rw [hg]
      rfl
    rw [burnsideA315y_alpha_apply, e.symm_apply_apply] at h1
    have h2 : g * l * g⁻¹ = l := by
      have h3 := congrArg Subtype.val (e.injective h1)
      simpa using h3
    calc l * g = g * l * g⁻¹ * g := by rw [h2]
      _ = g * l := by group
  rw [hC, Subgroup.mem_bot] at hc
  exact hc

theorem burnsideA315y_alpha_of_mem {G P : Type} [Group G] [Group P] (L : Subgroup G) [L.Normal]
    (e : ↥L ≃* P) (x : G) (hx : x ∈ L) :
    burnsideA315y_alpha L e x = MulAut.conj (e ⟨x, hx⟩) := by
  ext y
  rw [burnsideA315y_alpha_apply, MulAut.conj_apply]
  have h : MulAut.conjNormal x (e.symm y) = ⟨x, hx⟩ * e.symm y * (⟨x, hx⟩ : ↥L)⁻¹ :=
    Subtype.ext (by simp)
  rw [h, map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem burnsideA315y_map_alpha_L {G P : Type} [Group G] [Group P] (L : Subgroup G) [L.Normal]
    (e : ↥L ≃* P) :
    L.map (burnsideA315y_alpha L e) = (MulAut.conj : P →* MulAut P).range := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e ⟨x, hx⟩, (burnsideA315y_alpha_of_mem L e x hx).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(e.symm y : G), (e.symm y).2, ?_⟩
    rw [burnsideA315y_alpha_of_mem L e _ (e.symm y).2]
    simp

theorem burnsideA315y_map_alpha_of_le {G P : Type} [Group G] [Group P] (L : Subgroup G) [L.Normal]
    (e : ↥L ≃* P) {H : Subgroup G} (hH : H ≤ L) :
    H.map (burnsideA315y_alpha L e) =
      ((H.subgroupOf L).map e.toMonoidHom).map (MulAut.conj : P →* MulAut P) := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e ⟨x, hH hx⟩, ⟨⟨x, hH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩,
      (burnsideA315y_alpha_of_mem L e x (hH hx)).symm⟩
  · rintro ⟨y, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨(l : G), Subgroup.mem_subgroupOf.1 hl, burnsideA315y_alpha_of_mem L e _ l.2⟩

theorem burnsideA315y_exists_equiv_sylow {L P : Type} [Group L] [Group P] [Finite P] (e : L ≃* P)
    {Q : Subgroup L} {R : Subgroup P} (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q ⊤)
    (hR : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤) : ∃ e' : L ≃* P, Q.map e'.toMonoidHom = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index
    (CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_map_mulEquiv e hQ)
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (h1.toSylow h2) (h3.toSylow h4)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hR' : R = MulAut.conj g • Q.map e.toMonoidHom :=
    (congrArg (fun S : Sylow 2 P => (S : Subgroup P)) hg).symm
  rw [hR']
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨e q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩

theorem burnsideA315y_isSylowTwoOf_subgroupOf {G : Type} [Group G] {L T : Subgroup G} [L.Normal]
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
  have hsyl := burnsideA315x_sylow_inf (L := L) hT
  refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm, ?_⟩
  have h1 : (((T ⊓ L).subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
      ((T ⊓ L).subgroupOf L).index := by
    change ((T ⊓ L).subgroupOf L).relIndex ⊤ = _
    exact Subgroup.relIndex_top_right _
  rw [h1]
  exact hsyl.2.2

theorem burnsideA315y_exists_alpha_sylow {G P : Type} [Group G] [Group P] [Finite P]
    {L T : Subgroup G} [L.Normal] (e : ↥L ≃* P) (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {R : Subgroup P} (hR : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤) :
    ∃ e' : ↥L ≃* P,
      (T ⊓ L).map (burnsideA315y_alpha L e') = R.map (MulAut.conj : P →* MulAut P) := by
  obtain ⟨e', he'⟩ :=
    burnsideA315y_exists_equiv_sylow e (burnsideA315y_isSylowTwoOf_subgroupOf hT) hR
  exact ⟨e', by rw [burnsideA315y_map_alpha_of_le L e' inf_le_right, he']⟩

section Transport

variable {G X : Type} [Group G] [Group X] {α : G →* X}

theorem burnsideA315y_mem_normalizer_of_map (hα : Function.Injective α) {B : Subgroup G} {g : G}
    (h : α g ∈ Subgroup.normalizer ((B.map α : Subgroup X) : Set X)) :
    g ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro b
  have hb := h (α b)
  rwa [Subgroup.mem_map_iff_mem hα, ← map_inv, ← map_mul, ← map_mul,
    Subgroup.mem_map_iff_mem hα] at hb

theorem burnsideA315y_map_mem_centralizer {K : Subgroup G} {g : G}
    (h : g ∈ Subgroup.centralizer (K : Set G)) :
    α g ∈ Subgroup.centralizer ((K.map α : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at h ⊢
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_mul, ← map_mul, h k hk]

theorem burnsideA315y_mem_centralizer_of_map (hα : Function.Injective α) {K : Subgroup G} {g : G}
    (h : α g ∈ Subgroup.centralizer ((K.map α : Subgroup X) : Set X)) :
    g ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at h ⊢
  intro k hk
  apply hα
  rw [map_mul, map_mul]
  exact h (α k) (Subgroup.mem_map_of_mem α hk)

theorem burnsideA315y_map_inf_centralizer (hα : Function.Injective α) (I K : Subgroup G) :
    (I ⊓ Subgroup.centralizer (K : Set G)).map α =
      I.map α ⊓ Subgroup.centralizer ((K.map α : Subgroup X) : Set X) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxI, hxC⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem α hxI, burnsideA315y_map_mem_centralizer hxC⟩
  · rintro _ ⟨⟨x, hxI, rfl⟩, hxC⟩
    exact ⟨x, ⟨hxI, burnsideA315y_mem_centralizer_of_map hα hxC⟩, rfl⟩

theorem burnsideA315y_map_inf_normalizer (hα : Function.Injective α) (I U : Subgroup G) :
    (I ⊓ Subgroup.normalizer (U : Set G)).map α =
      I.map α ⊓ Subgroup.normalizer ((U.map α : Subgroup X) : Set X) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxI, hxN⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem α hxI,
      Subgroup.le_normalizer_map α (Subgroup.mem_map_of_mem α hxN)⟩
  · rintro _ ⟨⟨x, hxI, rfl⟩, hxN⟩
    exact ⟨x, ⟨hxI, burnsideA315y_mem_normalizer_of_map hα hxN⟩, rfl⟩

theorem burnsideA315y_isCyclic_of_map (hα : Function.Injective α) {H : Subgroup G}
    (h : IsCyclic ↥(H.map α)) : IsCyclic ↥H := by
  haveI := h
  exact isCyclic_of_surjective (H.equivMapOfInjective α hα).symm
    (H.equivMapOfInjective α hα).symm.surjective

theorem burnsideA315y_isSL2_of_map (hα : Function.Injective α) {p : ℕ} {K : Subgroup G}
    (h : CFSG.Quasithin.IsSL2 p ↥(K.map α)) : CFSG.Quasithin.IsSL2 p ↥K := by
  obtain ⟨f⟩ := h
  exact ⟨(K.equivMapOfInjective α hα).trans f⟩

theorem burnsideA315y_isElemAbelian_of_map (hα : Function.Injective α) {p n : ℕ}
    {B : Subgroup G} (h : CFSG.Quasithin.IsElemAbelianOfRank p n ↥(B.map α)) :
    CFSG.Quasithin.IsElemAbelianOfRank p n ↥B := by
  obtain ⟨f⟩ := h
  exact ⟨(B.equivMapOfInjective α hα).trans f⟩

theorem burnsideA315y_invertedIn_of_map (hα : Function.Injective α) {Y Z W : Subgroup G}
    (hZW : Z ≤ W) (h : CFSG.Quasithin.A315.InvertedIn (Y.map α) (Z.map α)) :
    CFSG.Quasithin.A315.InvertedIn Y W := by
  obtain ⟨_, ⟨t, htZ, rfl⟩, ht⟩ := h
  refine ⟨t, hZW htZ, fun x hx => hα ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv]
  exact ht (α x) (Subgroup.mem_map_of_mem α hx)

theorem burnsideA315y_isSylowOf_of_map (hα : Function.Injective α) {p : ℕ} {U L : Subgroup G}
    (h : CFSG.Quasithin.A315.IsSylowOf p (U.map α) (L.map α)) :
    CFSG.Quasithin.A315.IsSylowOf p U L := by
  obtain ⟨hUL, hUp, hUi⟩ := h
  refine ⟨(Subgroup.map_le_map_iff_of_injective hα).1 hUL,
    hUp.of_equiv (U.equivMapOfInjective α hα).symm, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective U L hα] at hUi

theorem burnsideA315y_isCartan_of_map (hα : Function.Injective α) {p : ℕ} {U I H : Subgroup G}
    (h : CFSG.Quasithin.A315.IsCartan p (U.map α) (I.map α) (H.map α)) :
    CFSG.Quasithin.A315.IsCartan p U I H := by
  obtain ⟨hle, hp, k, hk⟩ := h
  rw [← burnsideA315y_map_inf_normalizer hα I U] at hle hk
  refine ⟨(Subgroup.map_le_map_iff_of_injective hα).1 hle, ?_, k, ?_⟩
  · rwa [Subgroup.card_map_of_injective hα] at hp
  · rwa [Subgroup.relIndex_map_map_of_injective H _ hα] at hk

end Transport

theorem burnsideA315y_mem_of_odd {G : Type} [Group G] {B S : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ S ⊔ B)
    (hodd : Odd (orderOf x)) : x ∈ B := by
  haveI : (B.subgroupOf (S ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hSB
  let f : ↥S →* ↥(S ⊔ B) ⧸ B.subgroupOf (S ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf (S ⊔ B)) q
    have hy' : y ∈ (S : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S B hSB]
      exact hy
    obtain ⟨s, hs, b, hb, rfl⟩ := hy'
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨s, hs⟩) :
      ↥(S ⊔ B) ⧸ B.subgroupOf (S ⊔ B)) = QuotientGroup.mk ⟨s * b, hy⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hb
  have hQ : IsPGroup 2 (↥(S ⊔ B) ⧸ B.subgroupOf (S ⊔ B)) := hS.of_surjective f hf
  have hdvd : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥(S ⊔ B)) :
      ↥(S ⊔ B) ⧸ B.subgroupOf (S ⊔ B)) ∣ orderOf x := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (B.subgroupOf (S ⊔ B))) (⟨x, hx⟩ : ↥(S ⊔ B))
    rwa [Subgroup.orderOf_mk] at h1
  have h1 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥(S ⊔ B)) :
      ↥(S ⊔ B) ⧸ B.subgroupOf (S ⊔ B)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (hQ.orderOf_coprime (Nat.coprime_two_left.2 hodd) _) hdvd
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem burnsideA315y_le_normalizer {G : Type} [Group G] {L T B : Subgroup G} [hLn : L.Normal]
    (hT : IsPGroup 2 ↥T) (hBL : B ≤ L)
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) (hBodd : Odd (Nat.card ↥B))
    (hS : T ⊓ L ≤ Subgroup.normalizer (B : Set G)) : T ≤ Subgroup.normalizer (B : Set G) := by
  have key : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B := by
    intro t ht b hb
    have htb : t * b ∈ (B : Set G) * (T : Set G) := by
      rw [hperm]
      exact Set.mul_mem_mul ht hb
    obtain ⟨b₁, hb₁, t₁, ht₁, he⟩ := htb
    have he' : b₁ * t₁ = t * b := he
    have h4 : t * b * t⁻¹ = b₁ * (t₁ * t⁻¹) := by rw [← mul_assoc, he']
    have hs : t₁ * t⁻¹ ∈ T ⊓ L := by
      refine ⟨T.mul_mem ht₁ (T.inv_mem ht), ?_⟩
      have h2 : t₁ * t⁻¹ = b₁⁻¹ * (t * b * t⁻¹) := by rw [h4]; group
      rw [h2]
      exact L.mul_mem (L.inv_mem (hBL hb₁)) (hLn.conj_mem b (hBL hb) t)
    have hmem : t * b * t⁻¹ ∈ (T ⊓ L) ⊔ B := by
      rw [h4]
      exact mul_mem (Subgroup.mem_sup_right hb₁) (Subgroup.mem_sup_left hs)
    refine burnsideA315y_mem_of_odd (hT.to_le inf_le_left) hS hmem ?_
    have h5 : orderOf (t * b * t⁻¹) = orderOf b := by
      have h6 := MulEquiv.orderOf_eq (MulAut.conj t) b
      rwa [MulAut.conj_apply] at h6
    rw [h5, ← Subgroup.orderOf_mk b hb]
    exact Odd.of_dvd_nat hBodd (orderOf_dvd_natCard _)
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key t ht b, fun hb => ?_⟩
  have h6 := key t⁻¹ (T.inv_mem ht) _ hb
  have h7 : t⁻¹ * (t * b * t⁻¹) * t⁻¹⁻¹ = b := by group
  rwa [h7] at h6

theorem burnsideA315y_pullback {G X : Type} [Group G] [Group X] [Finite G]
    (α : G →* X) (hα : Function.Injective α) {L T B : Subgroup G} [L.Normal]
    (hT : IsPGroup 2 ↥T)
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) (hBodd : Odd (Nat.card ↥B))
    {δ : Bool} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : CFSG.Quasithin.IsPSLEps3 δ p 1 ↥L)
    (h : burnsideA315y_ModelConclusion X δ p (L.map α) (B.map α) ((T ⊓ L).map α)) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  rcases h with ⟨hδ, hBL', hE, hSN, hB0, hirr⟩ |
    ⟨K', hK'L, hK'SL, hBeq, hcyc1, hcyc2, ⟨H', U', hU', hH', hCH⟩, hcard, hlast⟩
  · left
    subst hδ
    have hBL : B ≤ L := (Subgroup.map_le_map_iff_of_injective hα).1 hBL'
    have hSB : T ⊓ L ≤ Subgroup.normalizer (B : Set G) := fun s hs =>
      burnsideA315y_mem_normalizer_of_map hα (hSN (Subgroup.mem_map_of_mem α hs))
    refine ⟨p, hp, hp2, hL, hBL, burnsideA315y_isElemAbelian_of_map hα hE, ?_⟩
    refine ⟨burnsideA315y_le_normalizer hT hBL hperm hBodd hSB, ?_, ?_⟩
    · intro hB
      apply hB0
      rw [hB, Subgroup.map_bot]
    · intro C hCB hTC
      have hSC : (T ⊓ L).map α ≤ Subgroup.normalizer ((C.map α : Subgroup X) : Set X) :=
        (Subgroup.map_mono (inf_le_left.trans hTC)).trans (Subgroup.le_normalizer_map α)
      rcases hirr (C.map α) (Subgroup.map_mono hCB) hSC with h0 | h0
      · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective C hα).1 h0)
      · exact Or.inr (Subgroup.map_injective hα h0)
  · right
    obtain ⟨K, rfl⟩ : ∃ K : Subgroup G, K.map α = K' :=
      ⟨K'.comap α, Subgroup.map_comap_eq_self (hK'L.trans (Subgroup.map_le_range α L))⟩
    obtain ⟨U, rfl⟩ : ∃ U : Subgroup G, U.map α = U' :=
      ⟨U'.comap α, Subgroup.map_comap_eq_self (hU'.1.trans (Subgroup.map_le_range α L))⟩
    obtain ⟨H, rfl⟩ : ∃ H : Subgroup G, H.map α = H' := by
      refine ⟨H'.comap α, Subgroup.map_comap_eq_self ?_⟩
      have h1 : H' ≤ L.map α ⊔ B.map α := hH'.1.trans inf_le_left
      rw [← Subgroup.map_sup] at h1
      exact h1.trans (Subgroup.map_le_range α _)
    rw [← Subgroup.map_sup] at hH'
    rw [← Subgroup.map_inf_eq B K α hα, ← burnsideA315y_map_inf_centralizer hα B K,
      ← Subgroup.map_sup] at hBeq
    rw [← Subgroup.map_inf_eq B K α hα] at hcyc1
    rw [← burnsideA315y_map_inf_centralizer hα B K] at hcyc2 hCH hcard
    rw [Subgroup.card_map_of_injective hα] at hcard
    rw [← Subgroup.map_inf_eq B K α hα, ← burnsideA315y_map_inf_centralizer hα B K,
      ← Subgroup.map_inf_eq (T ⊓ L) K α hα, ← burnsideA315y_map_inf_normalizer hα (T ⊓ L) B,
      ← burnsideA315y_map_inf_centralizer hα (T ⊓ L ⊓ Subgroup.normalizer (B : Set G))
        (B ⊓ Subgroup.centralizer (K : Set G)),
      Subgroup.card_map_of_injective hα] at hlast
    refine ⟨δ, p, hp, hp2, hL, K, (Subgroup.map_le_map_iff_of_injective hα).1 hK'L,
      burnsideA315y_isSL2_of_map hα hK'SL, Subgroup.map_injective hα hBeq,
      burnsideA315y_isCyclic_of_map hα hcyc1, burnsideA315y_isCyclic_of_map hα hcyc2,
      ⟨H, U, burnsideA315y_isSylowOf_of_map hα hU', burnsideA315y_isCartan_of_map hα hH',
        (Subgroup.map_le_map_iff_of_injective hα).1 hCH⟩, hcard, ?_⟩
    rcases hlast with ⟨hε, hinv⟩ | ⟨h8, h3, hinv⟩
    · exact Or.inl ⟨hε, burnsideA315y_invertedIn_of_map hα (inf_le_inf_right K inf_le_left) hinv⟩
    · exact Or.inr ⟨h8, h3, burnsideA315y_invertedIn_of_map hα le_rfl hinv⟩

theorem burnsideA315y_pullback_of_hyp {G P : Type} [Group G] [Group P] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) [L.Normal] (e : ↥L ≃* P) {δ : Bool} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : CFSG.Quasithin.IsPSLEps3 δ p 1 ↥L)
    (hM : burnsideA315y_ModelConclusion (MulAut P) δ p (L.map (burnsideA315y_alpha L e))
      (B.map (burnsideA315y_alpha L e)) ((T ⊓ L).map (burnsideA315y_alpha L e))) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  haveI := h.sqtk.finite
  exact burnsideA315y_pullback _
    (burnsideA315y_alpha_injective L e (burnsideA315x_centralizer_eq_bot h)) h.sylow.2.1 h.perm
    h.odd hp hp2 hL hM

end CFSG.ASVolI
