module

public import CFSG.Timmesfeld.Transvection.TriangleCrux

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem graph_conjSub (A : Subgroup G) (t g : G) :
    graph (conjSub A g) (g * t * g⁻¹) = conjSub (graph A t) g := by
  rw [graph, graph]
  conv_rhs => rw [conjSub, MonoidHom.map_closure]
  rw [graphSet, graphSet, Subgroup.coe_map, Set.image_image, Set.image_image]
  congr 2
  funext a
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem corrN_conjSub (A E : Subgroup G) (t g : G) :
    corrN (conjSub A g) (conjSub E g) (g * t * g⁻¹) = conjSub (corrN A E t) g := by
  rw [corrN, corrN, graph_conjSub]
  conv_rhs => rw [conjSub, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, f, hf, rfl⟩
    rw [← conjSub_sup_eq_sup] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨f₀, hf₀, rfl⟩ := hf
    refine ⟨x₀ * f₀ * x₀⁻¹, ⟨x₀, hx₀, f₀, hf₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨_, ⟨x₀, hx₀, f₀, hf₀, rfl⟩, rfl⟩
    refine ⟨g * x₀ * g⁻¹, ?_, g * f₀ * g⁻¹, conj_mem_conjSub g hf₀, ?_⟩
    · rw [← conjSub_sup_eq_sup]
      exact conj_mem_conjSub g hx₀
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

theorem conj (S : TriangleSetting Δ A E B t) (g : G) :
    TriangleSetting Δ (conjSub A g) (conjSub E g) (conjSub B g) (g * t * g⁻¹) where
  cls := S.cls
  iso := S.iso
  tri := ⟨S.cls.root.conjSub_mem S.tri.memA g, S.cls.root.conjSub_mem S.tri.memE g,
    S.cls.root.conjSub_mem S.tri.memB g, fun h => S.tri.ne (conjSub_injective g h),
    S.tri.comm.conjSub g, S.tri.oppA.conj g, S.tri.oppB.conj g⟩
  sq := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [S.sq, mul_one, mul_inv_cancel]
  centE := by
    rintro _ ⟨y, hy, rfl⟩
    exact (S.centE y hy).map (MulAut.conj g).toMonoidHom
  conjA := by
    rw [← conjSub_mul, show g * t * g⁻¹ * g = g * t by group, conjSub_mul, S.conjA]

omit [Group G] in
theorem conj_mem_sup {G : Type*} [Group G] {A E B : Subgroup G} {t : G}
    (htY : t ∈ A ⊔ E ⊔ B) (g : G) :
    g * t * g⁻¹ ∈ conjSub A g ⊔ conjSub E g ⊔ conjSub B g := by
  rw [← conjSub_sup_eq_sup, ← conjSub_sup_eq_sup]
  exact conj_mem_conjSub g htY

variable (S : TriangleSetting Δ A E B t)
include S

theorem conjSub_corrN_of_mem_sup [Finite G] {y : G} (hy : y ∈ A ⊔ E ⊔ B) :
    conjSub (corrN A E t) y = corrN A E t := by
  have hX : A ⊔ E ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (conjSub_corrN hx)
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e ∈ corrN A E t := corrM_le_corrN (S.partnerElt_mem_corrM he he1)
  have hB : B ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := by
    intro b hb
    rw [← S.conjSub_partnerElt he he1] at hb
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb
    have hs := Subgroup.le_normalizer hsN
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hX (Subgroup.mem_sup_left ha)))
      (Subgroup.inv_mem _ hs)
  exact conjSub_eq_self_iff.2 (sup_le hX hB hy)

theorem isPGroup_corrN [Finite G] (htY : t ∈ A ⊔ E ⊔ B) (hq : 4 ≤ Nat.card A) :
    IsPGroup 2 (corrN A E t) := fun n => ⟨1, Subtype.ext (by
  rw [pow_one, SubgroupClass.coe_pow, pow_two, S.mul_self_of_mem_corrN htY hq n.2]
  rfl)⟩

theorem sup_eq_sup_corrN [Finite G] : A ⊔ E ⊔ B = (A ⊔ E) ⊔ corrN A E t := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left S.corrN_le_sup)
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e ∈ corrN A E t := corrM_le_corrN (S.partnerElt_mem_corrM he he1)
  intro b hb
  have hb' : b ∈ conjSub A (partnerElt A E B e) := by
    rw [S.conjSub_partnerElt he he1]
    exact hb
  obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb'
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hsN)
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)))
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right hsN))

end TriangleSetting

theorem opposite_conjSub_of_ne (hΔ : IsTransvectionClass Δ) {P Q : Subgroup G} (hQ : Q ∈ Δ)
    (hQP : Opposite Q P) {x : G} (hx : x ∈ P ⊔ Q) (hne : conjSub P x ≠ P) :
    Opposite P (conjSub P x) := by
  rcases conjSub_eq_or_conjSub_eq hΔ hQ hQP hx with h | ⟨q, hq, h⟩
  · rw [h]
    exact hQP.symm
  · have hq1 : q ≠ 1 := by
      rintro rfl
      rw [conjSub_one] at h
      exact hne h
    rw [h, ← conjSub_partner hQP hq hq1]
    have := hQP.symm.conj (partner Q P q)
    rwa [conjSub_of_mem (partner_mem hQP hq hq1)] at this

theorem eq_bot_of_isPGroup [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    {A E : Subgroup G} (hA : A ∈ Δ) (hE : E ∈ Δ) (hEA : Opposite E A) {K : Subgroup G}
    (hK : IsPGroup 2 K) (hKX : K ≤ A ⊔ E) (hKn : ∀ x ∈ A ⊔ E, ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    K = ⊥ := by
  have hodd : ∀ {c : G}, c ∈ K → Odd (orderOf c) → c = 1 := by
    intro c hc hco
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hK) ⟨c, hc⟩
    rw [Subgroup.orderOf_mk] at hm
    rw [hm] at hco
    have hm0 : m = 0 := by
      by_contra h0
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [pow_succ] at hco
      exact (Nat.not_odd_iff_even.2 (even_two.mul_left (2 ^ m'))) hco
    rw [hm0, pow_zero] at hm
    exact orderOf_eq_one_iff.1 hm
  have hnorm : ∀ {P Q : Subgroup G}, P ∈ Δ → Q ∈ Δ → Opposite Q P → P ⊔ Q = A ⊔ E →
      ∀ k ∈ K, conjSub P k = P := by
    intro P Q hP hQ hQP hPQ k hk
    by_contra hne
    have hkX : k ∈ P ⊔ Q := hPQ ▸ hKX hk
    have hopp := opposite_conjSub_of_ne hΔ hQ hQP hkX hne
    obtain ⟨p, hp, hp1⟩ := hΔ.root.exists_ne_one hP
    have hpX : p ∈ A ⊔ E := hPQ ▸ Subgroup.mem_sup_left hp
    have hpp : p⁻¹ = p := inv_eq_of_mul_eq_one_right (hΔ.mul_self hP hp)
    have hkp : k * p * k⁻¹ ∈ conjSub P k := conj_mem_conjSub k hp
    have hkp1 : k * p * k⁻¹ ≠ 1 := fun h => hp1 (conj_eq_one_iff.1 h)
    have hc : p * (k * p * k⁻¹) ∈ K := by
      have : p * (k * p * k⁻¹) = (p * k * p⁻¹) * k⁻¹ := by rw [hpp]; group
      rw [this]
      exact K.mul_mem (hKn p hpX k hk) (K.inv_mem hk)
    have h1 := hodd hc (hopp.odd_orderOf_mul (hΔ.root.mul_self P hP) hp hp1 hkp hkp1)
    have h2 : k * p * k⁻¹ = p := by
      have h3 := eq_inv_of_mul_eq_one_right h1
      rwa [hpp] at h3
    exact hne (hΔ.eq_of_mem_of_mem hiso (hΔ.root.conjSub_mem hP k) hP hkp
      (by rw [h2]; exact hp) hkp1)
  have hA' := hnorm hA hE hEA rfl
  have hE' := hnorm hE hA hEA.symm (sup_comm E A)
  have hcomm : ∀ {P : Subgroup G}, P ≤ A ⊔ E → (∀ k ∈ K, conjSub P k = P) →
      (∀ p ∈ P, p ∈ K → p = 1) → ∀ k ∈ K, ∀ p ∈ P, Commute k p := by
    intro P hPX hPn hPK k hk p hp
    have h1 : k * p * k⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem (hPn k hk ▸ conj_mem_conjSub k hp) (P.inv_mem hp)
    have h2 : k * p * k⁻¹ * p⁻¹ ∈ K := by
      rw [show k * p * k⁻¹ * p⁻¹ = k * (p * k⁻¹ * p⁻¹) by group]
      exact K.mul_mem hk (hKn p (hPX hp) _ (K.inv_mem hk))
    have h3 := hPK _ h1 h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hkA := hcomm le_sup_left hA' fun a ha haK => hEA.symm.eq_one_of_conjSub_eq ha (hE' a haK)
  have hkE := hcomm le_sup_right hE' fun e he heK => hEA.eq_one_of_conjSub_eq he (hA' e heK)
  refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
  exact hEA.symm.eq_one_of_mem_centralizer (hΔ.root.mul_self A hA) (hKX hk)
    (Subgroup.mem_centralizer_iff.2 fun y hy =>
      (commute_of_mem_sup_of_commute (hkA k hk) (hkE k hk) hy).eq.symm)

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

theorem corrN_inf_sup_eq_bot [Finite G] (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (hq : 4 ≤ Nat.card A) : corrN A E t ⊓ (A ⊔ E) = ⊥ :=
  eq_bot_of_isPGroup S.cls S.iso S.tri.memA S.tri.memE S.tri.oppA
    ((S.isPGroup_corrN htY hq).to_le inf_le_left) inf_le_right fun _ hy _ hk =>
    ⟨conj_mem_corrN hy hk.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hk.2)
      (Subgroup.inv_mem _ hy)⟩

variable {A' E' B' : Subgroup G} {t' : G}

theorem corrN_le_of_sup_eq [Finite G] (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (S' : TriangleSetting Δ A' E' B' t') (htY' : t' ∈ A' ⊔ E' ⊔ B') (hq : 4 ≤ Nat.card A)
    (hX : A ⊔ E = A' ⊔ E') (hY : A ⊔ E ⊔ B = A' ⊔ E' ⊔ B') :
    corrN A' E' t' ≤ corrN A E t := by
  have hq' : 4 ≤ Nat.card A' := by rwa [S.cls.root.card_eq S'.tri.memA S.tri.memA]
  intro n' hn'
  have hXN : A ⊔ E ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (conjSub_corrN hx)
  have hn'Y : n' ∈ ((A ⊔ E ⊔ B : Subgroup G) : Set G) := hY ▸ S'.corrN_le_sup hn'
  rw [S.sup_eq_sup_corrN, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN] at hn'Y
  obtain ⟨x, hx, n, hn, hxn⟩ := hn'Y
  replace hxn : x * n = n' := hxn
  have hNN' : corrN A E t ≤ Subgroup.normalizer ((corrN A' E' t' : Subgroup G) : Set G) :=
    fun m hm => conjSub_eq_self_iff.1 (S'.conjSub_corrN_of_mem_sup (hY ▸ S.corrN_le_sup hm))
  have hK2 : IsPGroup 2 ↥((corrN A E t ⊔ corrN A' E' t') ⊓ (A ⊔ E)) :=
    (IsPGroup.to_sup_of_normal_right' (S.isPGroup_corrN htY hq) (S'.isPGroup_corrN htY' hq')
      hNN').to_le inf_le_left
  have hKn : ∀ y ∈ A ⊔ E, ∀ k ∈ (corrN A E t ⊔ corrN A' E' t') ⊓ (A ⊔ E),
      y * k * y⁻¹ ∈ (corrN A E t ⊔ corrN A' E' t') ⊓ (A ⊔ E) := by
    intro y hy k hk
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hk.2) (Subgroup.inv_mem _ hy)⟩
    have h1 : conjSub (corrN A E t ⊔ corrN A' E' t') y = corrN A E t ⊔ corrN A' E' t' := by
      rw [conjSub_sup_eq_sup, conjSub_corrN hy, conjSub_corrN (hX ▸ hy)]
    rw [← h1]
    exact conj_mem_conjSub y hk.1
  have hK := eq_bot_of_isPGroup S.cls S.iso S.tri.memA S.tri.memE S.tri.oppA hK2 inf_le_right hKn
  have hxK : x ∈ (corrN A E t ⊔ corrN A' E' t') ⊓ (A ⊔ E) := by
    refine ⟨?_, hx⟩
    rw [show x = n' * n⁻¹ by rw [← hxn]; group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn')
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ hn))
  rw [hK, Subgroup.mem_bot] at hxK
  rw [← hxn, hxK, one_mul]
  exact hn

theorem corrN_eq_of_sup_eq [Finite G] (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (S' : TriangleSetting Δ A' E' B' t') (htY' : t' ∈ A' ⊔ E' ⊔ B') (hq : 4 ≤ Nat.card A)
    (hX : A ⊔ E = A' ⊔ E') (hY : A ⊔ E ⊔ B = A' ⊔ E' ⊔ B') : corrN A E t = corrN A' E' t' := by
  have hq' : 4 ≤ Nat.card A' := by rwa [S.cls.root.card_eq S'.tri.memA S.tri.memA]
  exact le_antisymm (corrN_le_of_sup_eq S' htY' S htY hq' hX.symm hY.symm)
    (corrN_le_of_sup_eq S htY S' htY' hq hX hY)

end TriangleSetting

end CFSG.Timmesfeld.Transvection
