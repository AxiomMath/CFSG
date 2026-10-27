module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
import CFSG.GroupTheory.GL52.Simple
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section Gen

variable {G : Type} [Group G]

theorem s43_mem_cen {x g : G} (h : x * g = g * x) : g ∈ Cen x :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.symm

theorem s43_cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

theorem s43_mem_sup_of_comm {A H : Subgroup G} (hc : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a)
    {g : G} (hg : g ∈ A ⊔ H) : ∃ a ∈ A, ∃ h ∈ H, g = a * h := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ h ∈ H, g = a * h}
      mul_mem' := by
        rintro _ _ ⟨a, ha, h, hh, rfl⟩ ⟨a', ha', h', hh', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', h * h', H.mul_mem hh hh', ?_⟩
        have := hc a' ha' h hh
        calc a * h * (a' * h') = a * (h * a') * h' := by simp only [mul_assoc]
          _ = a * (a' * h) * h' := by rw [this]
          _ = a * a' * (h * h') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, H.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, h, hh, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, h⁻¹, H.inv_mem hh, ?_⟩
        have : Commute a h := hc a ha h hh
        rw [mul_inv_rev]
        exact ((this.inv_inv).symm.eq) }
  have hle : A ⊔ H ≤ S := by
    refine sup_le (fun a ha => ⟨a, ha, 1, H.one_mem, (mul_one a).symm⟩)
      (fun h hh => ⟨1, A.one_mem, h, hh, (one_mul h).symm⟩)
  exact hle hg

theorem s43_Jnorm {b : G} {J : Subgroup G} (hstd : FFStandardJ b J) {b₁ : G}
    (hb₁J : b₁ ∈ J) (hb₁o : orderOf b₁ = 3) :
    ∀ c ∈ Cen b, ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
  intro c hc j hj
  let φ : ↥(Cen b) ≃* ↥(Cen b) := MulAut.conj (⟨c, hc⟩ : ↥(Cen b))
  have hcomp : CFSG.IsComponent (J.subgroupOf (Cen b)) := hstd.2.1
  have hcomp' := CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp
  have hb₁C : b₁ ∈ Cen b := hstd.1 hb₁J
  have hmem : (⟨b₁, hb₁C⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hb₁J
  have hdvd : 3 ∣ Nat.card (J.subgroupOf (Cen b)) := by
    have := Subgroup.orderOf_dvd_natCard (J.subgroupOf (Cen b)) hmem
    rwa [Subgroup.orderOf_mk, hb₁o] at this
  have hdvd' : 3 ∣ Nat.card ((J.subgroupOf (Cen b)).map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have heq := hstd.2.2 _ hcomp' hdvd'
  have hjC : j ∈ Cen b := hstd.1 hj
  have hjK : (⟨j, hjC⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hj
  have : φ ⟨j, hjC⟩ ∈ (J.subgroupOf (Cen b)).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hjK, rfl⟩
  rw [heq] at this
  exact this

theorem s43_isElementaryAbelian_of_le {p : ℕ} {B A : Subgroup G} (hB : IsElementaryAbelian p B)
    (hAB : A ≤ B) : IsElementaryAbelian p A := by
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => by
    have h := congrArg (fun z : B => (z : G))
      (hB.toIsMulCommutative.is_comm.comm ⟨a.1, hAB a.2⟩ ⟨b.1, hAB b.2⟩)
    exact Subtype.ext h
  refine
    { is_comm := ⟨hcomm⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_ }
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := B) x.1 (hAB x.2))

end Gen

section Setup

variable {G : Type} [Group G] [Finite G]

theorem s43_center_gl5 : Subgroup.center (GL (Fin 5) (ZMod 2)) = ⊥ := by
  haveI : IsSimpleGroup (GL (Fin 5) (ZMod 2)) := CFSG.GroupTheory.GL52.isSimpleGroup_G52
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (GL (Fin 5) (ZMod 2))) with
    h | h
  · exact h
  · exfalso
    refine CFSG.GroupTheory.GL52.not_commutative_G52 fun a b => ?_
    have : b ∈ Subgroup.center (GL (Fin 5) (ZMod 2)) := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.mp this) a

theorem s43_center_of_equiv {J : Subgroup G} (e : J ≃* GL (Fin 5) (ZMod 2)) :
    Subgroup.center J = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have : e z ∈ Subgroup.center (GL (Fin 5) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e ((Subgroup.mem_center_iff.mp hz) x)
  rw [s43_center_gl5] at this
  exact e.injective (by simpa using this)

theorem s43_orders {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    orderOf b₁ = 3 ∧ orderOf b₂ = 3 ∧ b₁ * b₂ = b₂ * b₁ ∧ b₂ ∉ Subgroup.zpowers b₁ := by
  obtain ⟨hb₁3, hb₂3, hb₁b₂, hK1, hcardE, -⟩ := sec4_facts h4
  have hb₂1 : b₂ ≠ 1 := by
    rintro rfl
    exact hK1 (Subgroup.one_mem _)
  have hb₁1 : b₁ ≠ 1 := by
    intro h
    have hle : Subgroup.closure ({b₁, b₂} : Set G) ≤ Subgroup.zpowers b₂ := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [h]; exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardE, Nat.card_zpowers] at h1
    have h2 : orderOf b₂ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb₂3)
    omega
  exact ⟨orderOf_eq_prime hb₁3 hb₁1, orderOf_eq_prime hb₂3 hb₂1, hb₁b₂, hK1⟩

theorem setup_of_sec4 {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (e : J ≃* GL (Fin 5) (ZMod 2)) : Setup14 5 b J B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb₁3, hb₂3, hb₁b₂, hK1, hcardE, hE3⟩ := sec4_facts h4
  have hZ : Subgroup.center J = ⊥ := s43_center_of_equiv e
  obtain ⟨hJC, hcomp, huniq⟩ := h4.hyp.std
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hcomp.1
  obtain ⟨he27, hcardB⟩ := h4.mono.1
  haveI := he27
  have hBeq := h4.mono.2.1
  have hbo : orderOf b = 3 := h4.hyp.ord
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hb₁J : b₁ ∈ J := (Subgroup.mem_inf.mp h4.hb₁).2
  have hb₂J : b₂ ∈ J := (Subgroup.mem_inf.mp h4.hb₂).2
  have hBc : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (he27.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hb₁o : orderOf b₁ = 3 := (s43_orders h4).1
  have hJn := s43_Jnorm h4.hyp.std hb₁J hb₁o
  have hbJ : b ∉ J := by
    intro hbJ
    have : (⟨b, hbJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (s43_cen_comm (hJC g.2)).symm
    rw [hZ, Subgroup.mem_bot] at this
    have h1 : b = 1 := congrArg Subtype.val this
    rw [h1, orderOf_one] at hbo
    omega
  have hEle : Subgroup.closure ({b₁, b₂} : Set G) ≤ B ⊓ J := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h4.hb₁
    · exact h4.hb₂
  have hcard9 : Nat.card ↥(B ⊓ J) = 3 ^ 2 := by
    have hd1 : 3 ^ 2 ∣ Nat.card ↥(B ⊓ J) := by
      rw [← hcardE]; exact Subgroup.card_dvd_of_le hEle
    have hd2 : Nat.card ↥(B ⊓ J) ∣ 3 ^ 3 := by
      rw [← hcardB]; exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(B ⊓ J) ≠ 3 ^ 3 := by
      intro h27
      have heq : B ⊓ J = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hcardB])
      exact hbJ ((heq ▸ inf_le_right : B ≤ J) hbB)
    obtain ⟨k, hk, hkv⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
    have hk2 : 2 ≤ k := by
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp (hkv ▸ hd1)
      exact this
    interval_cases k
    · exact hkv
    · exact absurd hkv hne
  have he9 : IsElemAb 3 2 (B ⊓ J) :=
    ⟨s43_isElementaryAbelian_of_le he27 inf_le_left, hcard9⟩
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
  have hzJ : Subgroup.zpowers b ⊓ (B ⊓ J) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxz, hxB, hxJ⟩
    by_contra hne
    apply hbJ
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have : b ^ 3 = 1 := hbo ▸ pow_orderOf_eq_one b
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hne
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hxz
    have heq : Subgroup.zpowers x = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hbo])
    have : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.mpr hxJ) this
  have hcommzB : ∀ u ∈ Subgroup.zpowers b, ∀ v ∈ B ⊓ J, u * v = v * u := fun u hu v hv =>
    hBc u (hzB hu) v hv.1
  have hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B := by
    obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommzB
    rw [hzJ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hbo, hcard9] at hprod
    exact Subgroup.eq_of_le_of_card_ge (sup_le hzB inf_le_left)
      (by rw [hprod, hcardB]; norm_num)
  have hbC : b ∈ CenS J := Subgroup.mem_centralizer_iff.mpr fun j hj =>
    (s43_cen_comm (hJC hj)).symm
  have hBC : B ⊓ CenS J = Subgroup.zpowers b := by
    refine le_antisymm ?_ (le_inf hzB (Subgroup.zpowers_le.mpr hbC))
    rintro x ⟨hxB, hxC⟩
    have hx : x ∈ Subgroup.zpowers b ⊔ (B ⊓ J) := by rw [hsup]; exact hxB
    obtain ⟨a, ha, u, hu, rfl⟩ := s43_mem_sup_of_comm hcommzB hx
    have hu' : u ∈ CenS J := by
      have := (CenS J).mul_mem ((CenS J).inv_mem ((Subgroup.zpowers_le.mpr hbC) ha)) hxC
      simpa using this
    have : (⟨u, hu.2⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hu' g g.2)
    rw [hZ, Subgroup.mem_bot] at this
    have h1 : u = 1 := congrArg Subtype.val this
    rw [h1, mul_one]
    exact ha
  exact ⟨Or.inr rfl, h4.hyp, h4.sylB, hq, hJn, L14.isSylowOf_inf_normal h4.sylB hJC hJn,
    ⟨he27, hcardB⟩, he9, hsup, hBC, by rw [hZ, Subgroup.card_bot]; exact one_dvd 2⟩

end Setup

end CFSG.RankThree.PartTwo.Sec21.FF79
