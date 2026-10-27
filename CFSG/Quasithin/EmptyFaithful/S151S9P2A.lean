module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin

namespace HSRuLoc

namespace Lift

open CFSG.Open
open scoped Pointwise commutatorElement

section Basic

variable {X H : Type*} [Group X] [Group H]

theorem card_eq_card_map_mul_card_ker [Finite X] (f : X →* H) {A : Subgroup X} (h : f.ker ≤ A) :
    Nat.card A = Nat.card (A.map f) * Nat.card f.ker := by
  let g : ↥A →* H := f.domRestrict A
  have hrange : g.range = A.map f := MonoidHom.domRestrict_range A f
  have hker : g.ker = f.ker.subgroupOf A := MonoidHom.ker_domRestrict A f
  have h1 : Nat.card A = Nat.card (↥A ⧸ g.ker) * Nat.card g.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have h2 : Nat.card (↥A ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.ker = Nat.card f.ker := by
    rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h1, h2, h3, hrange]

theorem map_comap_eq_of_uniq [Finite X] (π : X →* H) (hπ : Function.Surjective π)
    {Kb P : Subgroup H} (T₀ : Subgroup X) (hP : T₀.map π = P) (hPK : P ≤ Kb)
    (huniq : ∀ Y : Subgroup H, P ≤ Y → Nat.card Y = Nat.card Kb → Y = Kb)
    (φ : X ≃* X) (hker : π.ker.map φ.toMonoidHom = π.ker)
    (hT : T₀ ≤ T₀.map φ.toMonoidHom) :
    (Kb.comap π).map φ.toMonoidHom = Kb.comap π := by
  set Kt := Kb.comap π with hKt
  have hkerKt : π.ker ≤ Kt := fun x hx => by
    rw [hKt, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]; exact Kb.one_mem
  have hkerφ : π.ker ≤ Kt.map φ.toMonoidHom := hker ▸ Subgroup.map_mono hkerKt
  have hmapKt : Kt.map π = Kb := Subgroup.map_comap_eq_self_of_surjective hπ Kb
  have hcard1 := card_eq_card_map_mul_card_ker π hkerKt
  have hcard2 : Nat.card ↥(Kt.map φ.toMonoidHom) = Nat.card ↥Kt :=
    Subgroup.card_map_of_injective φ.injective
  have hcard3 := card_eq_card_map_mul_card_ker π hkerφ
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  have hY : Nat.card ↥((Kt.map φ.toMonoidHom).map π) = Nat.card Kb := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← hcard3, hcard2, hcard1, hmapKt]
  have hTK : T₀ ≤ Kt := fun t ht => by
    have : π t ∈ P := hP ▸ Subgroup.mem_map_of_mem π ht
    exact hPK this
  have hPY : P ≤ (Kt.map φ.toMonoidHom).map π := by
    rw [← hP]
    exact Subgroup.map_mono (hT.trans (Subgroup.map_mono hTK))
  have hYK : (Kt.map φ.toMonoidHom).map π = Kb := huniq _ hPY hY
  calc Kt.map φ.toMonoidHom = ((Kt.map φ.toMonoidHom).map π).comap π :=
        (Subgroup.comap_map_eq_self hkerφ).symm
    _ = Kb.comap π := by rw [hYK]

end Basic

section Index

variable {G : Type*} [Group G]

theorem relIndex_sup_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

theorem isSylowTwoOf_sup {K L S : Subgroup G} (hKL : K ≤ L)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hS2 : IsPGroup 2 ↥S)
    (hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (K ⊔ S) := by
  refine ⟨le_sup_right, hS2, ?_⟩
  have h1 : (S.subgroupOf (K ⊔ S)).index = S.relIndex (K ⊔ S) := rfl
  have hT : S ⊓ L ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans hSK
  have h2 : S.relIndex (K ⊔ S) = (S ⊓ L).relIndex (K ⊔ (S ⊓ L)) := by
    rw [relIndex_sup_of_le_normalizer hSK, relIndex_sup_of_le_normalizer hT]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hKL x.2⟩, fun h => h.1⟩
  have h3 : (S ⊓ L).relIndex (K ⊔ (S ⊓ L)) * (K ⊔ (S ⊓ L)).relIndex L = (S ⊓ L).relIndex L :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hKL inf_le_right)
  rw [h1, h2]
  intro h2d
  apply hsyl.2.2
  rw [← (show (S ⊓ L).relIndex L = ((S ⊓ L).subgroupOf L).index from rfl), ← h3]
  exact Dvd.dvd.mul_right h2d _

end Index

section SL

theorem card_statedSL3 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem not_isPGroup_statedSL3 :
    ¬ IsPGroup 2 ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
  intro h
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp h
  rw [card_statedSL3] at hn
  have h3 : 3 ∣ 2 ^ n := (show 3 ∣ 168 by norm_num).trans hn
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem isSimpleGroup_statedSL3 :
    IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
  CFSG.Quasithin.Vol2.Ch10.SecA.isSimpleGroup_statedSL_two (n := 3) (by norm_num)

end SL

section Group

variable {X H : Type*} [Group X] [Group H]

theorem le_ker_of_normal_isPGroup {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hS : ¬ IsPGroup 2 S) (a : Y →* S) (ha : Function.Surjective a) {B : Subgroup Y}
    [hBn : B.Normal] (hB : IsPGroup 2 B) : B ≤ a.ker := by
  have hnorm : (B.map a).Normal := Subgroup.Normal.map hBn a ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.map a) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    apply hS
    have hB2 : IsPGroup 2 (B.map a) := hB.map a
    rw [h] at hB2
    exact hB2.of_equiv Subgroup.topEquiv

theorem commutator_mul_central_left {x y c : X} (hc : c ∈ Subgroup.center X) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  have h1 : c * y * c⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]
  calc ⁅x * c, y⁆ = x * (c * y * c⁻¹) * x⁻¹ * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅x, y⁆ := by rw [h1]; simp [commutatorElement_def, mul_assoc]

theorem commutator_mul_central_right {x y c : X} (hc : c ∈ Subgroup.center X) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have h1 : c * x⁻¹ * c⁻¹ = x⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hc x⁻¹, mul_inv_cancel_right]
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹ * c⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅x, y⁆ := by rw [h1]; simp [commutatorElement_def, mul_assoc]

theorem commutator_mul_central {x y c c' : X} (hc : c ∈ Subgroup.center X)
    (hc' : c' ∈ Subgroup.center X) : ⁅x * c, y * c'⁆ = ⁅x, y⁆ := by
  rw [commutator_mul_central_left hc, commutator_mul_central_right hc']

theorem map_commutator_comap (π : X →* H) (hπ : Function.Surjective π)
    {Kb : Subgroup H} (hperf : ⁅Kb, Kb⁆ = Kb) :
    (⁅Kb.comap π, Kb.comap π⁆).map π = Kb := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ, hperf]

theorem commutator_commutator_comap (π : X →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) {Kb : Subgroup H} (hperf : ⁅Kb, Kb⁆ = Kb) :
    ⁅⁅Kb.comap π, Kb.comap π⁆, ⁅Kb.comap π, Kb.comap π⁆⁆ = ⁅Kb.comap π, Kb.comap π⁆ := by
  have h1 := map_commutator_comap π hπ hperf
  generalize hKt : Kb.comap π = Kt at h1 ⊢
  have hmem : ∀ z, z ∈ Kt → π z ∈ Kb := fun z hz => by rw [← hKt] at hz; exact hz
  generalize hD : ⁅Kt, Kt⁆ = D at h1 ⊢
  have hle : ⁅D, D⁆ ≤ D := Subgroup.commutator_le.mpr fun g hg h hh =>
    D.mul_mem (D.mul_mem (D.mul_mem hg hh) (D.inv_mem hg)) (D.inv_mem hh)
  refine le_antisymm hle ?_
  have hdec : ∀ z ∈ Kt, ∃ d ∈ D, ∃ c ∈ Subgroup.center X, z = d * c := by
    intro z hz
    have : π z ∈ D.map π := by rw [h1]; exact hmem z hz
    obtain ⟨d, hd, hdz⟩ := this
    refine ⟨d, hd, d⁻¹ * z, hker ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdz, inv_mul_cancel]
  rw [← hD]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨d, hd, c, hc, rfl⟩ := hdec x hx
  obtain ⟨d', hd', c', hc', rfl⟩ := hdec y hy
  rw [commutator_mul_central hc hc', hD]
  exact Subgroup.commutator_mem_commutator hd hd'

theorem ker_le_center_aux (π : X →* H) (hπ : Function.Surjective π)
    (hX : IsSimpleGroup (X ⧸ Subgroup.center X)) (hZ : IsPGroup 2 ↥(Subgroup.center X))
    (hH : ¬ IsPGroup 2 H) : π.ker ≤ Subgroup.center X := by
  have hN : π.ker.Normal := inferInstance
  let q := QuotientGroup.mk' (Subgroup.center X)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hnorm : (π.ker.map q).Normal := Subgroup.Normal.map hN q hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.ker.map q) with h | h
  · exact ((Subgroup.map_eq_bot_iff _).mp h).trans (le_of_eq (QuotientGroup.ker_mk' _))
  · exfalso
    apply hH
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    have hx : q x ∈ π.ker.map q := h ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := hx
    have hz : n⁻¹ * x ∈ Subgroup.center X := QuotientGroup.eq.mp hnx
    obtain ⟨k, hk⟩ := hZ ⟨n⁻¹ * x, hz⟩
    refine ⟨k, ?_⟩
    have hπx : π x = π (n⁻¹ * x) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
    rw [hπx, ← map_pow]
    have : (n⁻¹ * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this, map_one]

theorem pCoreOf_eq_inf_comap [Finite X] (π : X →* H) (hker2 : IsPGroup 2 ↥π.ker)
    {D : Subgroup X} {Kb Rb : Subgroup H} (hD : D.map π = Kb) (hRK : Rb ≤ Kb)
    (hRn : (Rb.subgroupOf Kb).Normal) (hR2 : IsPGroup 2 ↥Rb)
    {S : Type*} [Group S] [IsSimpleGroup S] (hS : ¬ IsPGroup 2 S)
    (a : ↥Kb →* S) (ha : Function.Surjective a) (hak : a.ker = Rb.subgroupOf Kb) :
    pCoreOf 2 D = D ⊓ Rb.comap π := by
  have hN2 : IsPGroup 2 ↥(D ⊓ Rb.comap π) := (hR2.comap_of_ker_isPGroup π hker2).to_inf_right
  have hRconj : ∀ k ∈ Kb, ∀ r ∈ Rb, k * r * k⁻¹ ∈ Rb := by
    intro k hk r hr
    have := hRn.conj_mem ⟨r, hRK hr⟩ (by simpa [Subgroup.mem_subgroupOf] using hr) ⟨k, hk⟩
    simpa [Subgroup.mem_subgroupOf] using this
  apply le_antisymm
  · have hOD : pCoreOf 2 D ≤ D := Subgroup.map_subtype_le _
    have hDnorm : D ≤ Subgroup.normalizer (pCoreOf 2 D : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D
    have hO2 : IsPGroup 2 ↥(pCoreOf 2 D) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D
    set O := pCoreOf 2 D with hO
    set B := O.map π with hB
    have hBK : B ≤ Kb := hD ▸ Subgroup.map_mono hOD
    have hB2 : IsPGroup 2 ↥B := hO2.map π
    have hB'n : (B.subgroupOf Kb).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := hn
      have hg : (g : H) ∈ D.map π := hD ▸ g.2
      obtain ⟨d, hd, hdg⟩ := hg
      refine ⟨d * o * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDnorm hd) o).mp ho, ?_⟩
      simp [hdg, hon]
    have hB'2 : IsPGroup 2 ↥(B.subgroupOf Kb) := hB2.comap_subtype
    have hle := le_ker_of_normal_isPGroup hS a ha hB'2
    intro o ho
    refine ⟨hOD ho, ?_⟩
    have h1 : (⟨π o, hBK (Subgroup.mem_map_of_mem π ho)⟩ : ↥Kb) ∈ B.subgroupOf Kb :=
      Subgroup.mem_map_of_mem π ho
    have h2 := hle h1
    rw [hak, Subgroup.mem_subgroupOf] at h2
    exact h2
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hN2
    have hconj : ∀ d ∈ D, ∀ n ∈ D ⊓ Rb.comap π, d * n * d⁻¹ ∈ D ⊓ Rb.comap π := by
      intro d hd n hn
      refine ⟨D.mul_mem (D.mul_mem hd hn.1) (D.inv_mem hd), ?_⟩
      show π (d * n * d⁻¹) ∈ Rb
      rw [map_mul, map_mul, map_inv]
      exact hRconj (π d) (hD ▸ Subgroup.mem_map_of_mem π hd) (π n) hn.2
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj d hd n hn, fun hn => ?_⟩
    have := hconj d⁻¹ (D.inv_mem hd) _ hn
    simpa [mul_assoc] using this

theorem map_pCoreOf_subtype (L : Subgroup X) (K : Subgroup L) :
    (pCoreOf 2 K).map L.subtype = pCoreOf 2 (K.map L.subtype) := by
  set e : K ≃* K.map L.subtype := K.equivMapOfInjective L.subtype L.subtype_injective with he
  rw [pCoreOf, pCoreOf, Subgroup.map_map, ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e,
    Subgroup.map_map]
  rfl

end Group

end Lift

end HSRuLoc

end CFSG.Quasithin
