module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13a
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts14
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base

import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 L14

variable {G : Type} [Group G] [Finite G]

private theorem l14_mem_cen {x g : G} (h : x * g = g * x) : g ∈ Cen x :=
  Subgroup.mem_centralizer_singleton_iff.mpr h.symm

private theorem l14_cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

private theorem l14_Jnorm {b : G} {J : Subgroup G} (hstd : FFStandardJ b J) {b₁ : G}
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

private theorem l14_mem_sup_of_comm {A H : Subgroup G} (hc : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a)
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
        exact ((this.inv_inv).symm.eq)  }
  have hle : A ⊔ H ≤ S := by
    refine sup_le (fun a ha => ⟨a, ha, 1, H.one_mem, (mul_one a).symm⟩)
      (fun h hh => ⟨1, A.one_mem, h, hh, (one_mul h).symm⟩)
  exact hle hg

private theorem l14_mem_cenS_sup {K₁ K₂ : Subgroup G} {z : G} (h₁ : z ∈ CenS K₁)
    (h₂ : z ∈ CenS K₂) : z ∈ CenS (K₁ ⊔ K₂) := by
  have hle : K₁ ⊔ K₂ ≤ Cen z := by
    refine sup_le (fun k hk => l14_mem_cen ?_) (fun k hk => l14_mem_cen ?_)
    · exact (Subgroup.mem_centralizer_iff.mp h₁ k hk).symm
    · exact (Subgroup.mem_centralizer_iff.mp h₂ k hk).symm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (l14_cen_comm (hle hk)).symm

structure Setup14 (n : ℕ) (b : G) (J B : Subgroup G) : Prop where
  hn : n = 4 ∨ n = 5
  hyp : FF79Hyp n b J
  hB : IsSylowOf 3 B (Cen b)
  hq : CFSG.IsQuasisimple ↥J
  hJn : ∀ c ∈ Cen b, ∀ j ∈ J, c * j * c⁻¹ ∈ J
  hB0 : IsSylowOf 3 (B ⊓ J) J
  e27 : IsElemAb 3 3 B
  e9 : IsElemAb 3 2 (B ⊓ J)
  hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B
  hBC : B ⊓ CenS J = Subgroup.zpowers b
  hZ : Nat.card ↥(Subgroup.center ↥J) ∣ 2

theorem setup14 (hK : FF79KTypeLn) (hCJ : FF79KCenterJ) {n : ℕ} (hn : n = 4 ∨ n = 5)
    {b : G} {J : Subgroup G} (h : FF79Hyp n b J) {B : Subgroup G}
    (hB : IsSylowOf 3 B (Cen b)) : Setup14 n b J B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e27, e9, hsup, hBC⟩ := ff79_1_3_struct hK hn h hB
  obtain ⟨hJC, hcomp, huniq⟩ := h.std
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hcomp.1
  have h3 : 3 ∣ Nat.card ↥(B ⊓ J) := by
    rw [e9.2]; exact dvd_pow_self 3 (by norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ J)) 3 h3
  have htJ : (t : G) ∈ J := t.2.2
  have hto : orderOf (t : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ht
  have hJn := l14_Jnorm h.std htJ hto
  have hBJ : IsSylowOf 3 (B ⊓ J) J := isSylowOf_inf_normal hB hJC hJn
  exact ⟨hn, h, hB, hq, hJn, hBJ, e27, e9, hsup, hBC, hCJ G n J hn hq h.model⟩

private theorem l14_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

namespace Setup14

variable {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B)
include S

theorem J_le_cen : J ≤ Cen b := S.hyp.std.1

theorem cen_le_nor : Cen b ≤ Nor J := by
  intro x hx
  refine Subgroup.mem_set_normalizer_iff.mpr (fun y => ⟨fun hy => S.hJn x hx y hy, fun hy => ?_⟩)
  have := S.hJn x⁻¹ (Subgroup.inv_mem _ hx) _ hy
  have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
  rw [e] at this
  exact this

theorem b_mem_B : b ∈ B := S.hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)

theorem B_comm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
  congrArg Subtype.val (S.e27.1.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem B_le_cen : B ≤ Cen b := S.hB.1

theorem B_le_cenS_B : B ≤ CenS B := fun u hu =>
  Subgroup.mem_centralizer_iff.mpr (fun v hv => S.B_comm v hv u hu)

theorem exists_order3 : ∃ t ∈ B ⊓ J, orderOf t = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥(B ⊓ J) := by
    rw [S.e9.2]; exact dvd_pow_self 3 (by norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ J)) 3 h3
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩

theorem hZ3 : Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) :=
  Nat.Coprime.coprime_dvd_right S.hZ (by norm_num)

theorem X_le_cenS (hX : Odd (Nat.card (Opp 3 (Cen b)))) : Opp 3 (Cen b) ≤ CenS J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc := S.J_le_cen
  set X := Opp 3 (Cen b) with hXdef
  have hI : ((X ⊓ J).subgroupOf J).Normal := ⟨fun u hu h => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    show (h : G) * u * (h : G)⁻¹ ∈ X ⊓ J
    exact ⟨Opp_conj_mem (hJc h.2) hu.1, J.mul_mem (J.mul_mem h.2 hu.2) (J.inv_mem h.2)⟩⟩
  have hcard : Nat.card ↥(X ⊓ J) = 1 := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups S.hq hI with htop | hcen
    · exfalso
      obtain ⟨t, ht, hto⟩ := S.exists_order3
      have htJ : t ∈ J := ht.2
      have : (⟨t, htJ⟩ : ↥J) ∈ (X ⊓ J).subgroupOf J := by rw [htop]; trivial
      have htX : t ∈ X := (Subgroup.mem_subgroupOf.mp this).1
      have h3 := Subgroup.orderOf_dvd_natCard X htX
      rw [hto] at h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Opp_coprime 3 _) h3
    · have hle : X ⊓ J ≤ (Subgroup.center ↥J).map J.subtype := by
        intro z hz
        have : (⟨z, hz.2⟩ : ↥J) ∈ (X ⊓ J).subgroupOf J := hz
        exact ⟨⟨z, hz.2⟩, hcen this, rfl⟩
      have hd1 : Nat.card ↥(X ⊓ J) ∣ 2 := by
        have := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective J.subtype_injective] at this
        exact this.trans S.hZ
      have hd2 : Nat.card ↥(X ⊓ J) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
      have hodd : Odd (Nat.card ↥(X ⊓ J)) := hX.of_dvd_nat hd2
      rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hxc : x ∈ Cen b := Opp_le 3 _ hx
  have hjc : j ∈ Cen b := hJc hj
  have hc : x * j * x⁻¹ * j⁻¹ ∈ X ⊓ J := by
    refine ⟨?_, J.mul_mem (S.hJn x hxc j hj) (J.inv_mem hj)⟩
    have h2 := X.mul_mem hx (Opp_conj_mem hjc (X.inv_mem hx))
    simpa [mul_assoc] using h2
  rw [(Subgroup.eq_bot_iff_card (X ⊓ J)).mpr hcard, Subgroup.mem_bot] at hc
  have h3 := mul_inv_eq_one.mp hc
  exact (mul_inv_eq_iff_eq_mul.mp h3).symm

theorem C0_norm : ∀ g ∈ Cen b, ∀ c ∈ Cen b ⊓ CenS J, g * c * g⁻¹ ∈ Cen b ⊓ CenS J := by
  intro g hg c hc
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hc.1) (Subgroup.inv_mem _ hg), ?_⟩
  show g * c * g⁻¹ ∈ CenS J
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hj' : g⁻¹ * j * g ∈ J := by simpa using S.hJn g⁻¹ (Subgroup.inv_mem _ hg) j hj
  have hcj := Subgroup.mem_centralizer_iff.mp hc.2 _ hj'
  calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [hcj]
    _ = g * c * g⁻¹ * j := by group

theorem C0_decomp : ∀ c ∈ Cen b ⊓ CenS J, ∃ i : ℤ, ∃ x ∈ Opp 3 (Cen b), c = b ^ i * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ := Cen b ⊓ CenS J with hC₀
  have hBsyl : IsSylowOf 3 (B ⊓ C₀) C₀ := isSylowOf_inf_normal S.hB inf_le_left S.C0_norm
  have hBeq : B ⊓ C₀ = Subgroup.zpowers b := by
    rw [← S.hBC]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, S.B_le_cen h.1, h.2⟩⟩
  rw [hBeq] at hBsyl
  have hP0p : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf C₀) := hBsyl.2.1.comap_subtype
  have hidx : ¬ 3 ∣ ((Subgroup.zpowers b).subgroupOf C₀).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hBsyl.2.2
  let P : Sylow 3 ↥C₀ := hP0p.toSylow hidx
  have hPc : (P : Subgroup ↥C₀) ≤ Subgroup.center ↥C₀ := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    have hp' : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
    have hbq : b ∈ Cen (q : G) := l14_mem_cen (l14_cen_comm q.2.1).symm
    have hpq : (p : G) ∈ Cen (q : G) := (Subgroup.zpowers_le.mpr hbq) hp'
    exact Subtype.ext (l14_cen_comm hpq)
  have hcomp := CFSG.FullDefectCanonical.pPrimeCore_isComplement_of_central P hPc
  intro c hc
  obtain ⟨⟨⟨m, hm⟩, ⟨p, hp⟩⟩, hx, -⟩ := hcomp.existsUnique (⟨c, hc⟩ : ↥C₀)
  have hmX : (m : G) ∈ Opp 3 (Cen b) :=
    Opp_le_Opp_of_normalized inf_le_left S.C0_norm (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
  have hpZ : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hpZ
  refine ⟨i, m, hmX, ?_⟩
  have hc' : c = m * p := (congrArg Subtype.val hx).symm
  rw [hc', ← hi]
  have hmc : (m : G) ∈ Cen b := Opp_le 3 _ hmX
  exact (((show Commute b m from l14_cen_comm hmc).zpow_left i).symm).eq

theorem X_le_C0 (hX : Odd (Nat.card (Opp 3 (Cen b)))) : Opp 3 (Cen b) ≤ Cen b ⊓ CenS J :=
  le_inf (Opp_le 3 _) (S.X_le_cenS hX)

theorem b_mem_C0 : b ∈ Cen b ⊓ CenS J :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_centralizer_iff.mpr fun j hj => (l14_cen_comm (S.J_le_cen hj)).symm⟩

theorem C0_eq (hX : Odd (Nat.card (Opp 3 (Cen b)))) :
    Cen b ⊓ CenS J = Subgroup.zpowers b ⊔ Opp 3 (Cen b) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨i, x, hx, rfl⟩ := S.C0_decomp c hc
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i)) (Subgroup.mem_sup_right hx)
  · exact sup_le (Subgroup.zpowers_le.mpr S.b_mem_C0) (S.X_le_C0 hX)

theorem card_C0 (hX : Odd (Nat.card (Opp 3 (Cen b)))) :
    Nat.card ↥(Cen b ⊓ CenS J) = 3 * Nat.card (Opp 3 (Cen b)) := by
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Opp 3 (Cen b), x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute b y from l14_cen_comm (Opp_le 3 _ hy)).zpow_left i).eq
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have h2 : Nat.card ↥(Subgroup.zpowers b ⊓ Opp 3 (Cen b)) = 1 := by
    have d1 : Nat.card ↥(Subgroup.zpowers b ⊓ Opp 3 (Cen b)) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ Opp 3 (Cen b) ≤
        Subgroup.zpowers b)
      rwa [Nat.card_zpowers, S.hyp.ord] at this
    have d2 : Nat.card ↥(Subgroup.zpowers b ⊓ Opp 3 (Cen b)) ∣ Nat.card (Opp 3 (Cen b)) :=
      Subgroup.card_dvd_of_le inf_le_right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Nat.eq_one_of_dvd_coprimes (Opp_coprime 3 _) d1 d2
  rw [h2, mul_one, Nat.card_zpowers, S.hyp.ord] at h1
  rw [S.C0_eq hX]
  exact h1

theorem cenB_le_cen : CenS B ≤ Cen b :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.b_mem_B)

theorem C0_le_cenB : Cen b ⊓ CenS J ≤ CenS B := by
  intro c hc
  rw [← S.hsup]
  refine l14_mem_cenS_sup ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute b c from l14_cen_comm hc.1).zpow_left i).eq
  · exact Subgroup.centralizer_le (fun x hx => hx.2) hc.2

theorem inf_cenS_card_dvd : Nat.card ↥(J ⊓ CenS J) ∣ Nat.card ↥(Subgroup.center ↥J) := by
  have hle : J ⊓ CenS J ≤ (Subgroup.center ↥J).map J.subtype := by
    rintro z ⟨hzJ, hzC⟩
    refine ⟨⟨z, hzJ⟩, ?_, rfl⟩
    show (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
  have hd := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective J.subtype_injective] at hd

theorem index_data (hX : Odd (Nat.card (Opp 3 (Cen b)))) (hAC : FF79KAutCentP) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ (Opp 3 (Cen b)).relIndex (CenS B) = 27 * k ∧
      Nat.card ↥(CenS B) = 27 * k * Nat.card (Opp 3 (Cen b)) ∧
      (k = 1 → CenS B = (B ⊓ J) ⊔ (Cen b ⊓ CenS J)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Opp 3 (Cen b) with hXdef
  set D := CenS B with hD
  set B₀ := B ⊓ J with hB₀
  set C₀ := Cen b ⊓ CenS J with hC₀
  set M := B₀ ⊔ CenS J with hM
  set H := Nor J ⊓ CenS B₀ with hH
  have hDH : D ≤ H := le_inf (S.cenB_le_cen.trans S.cen_le_nor)
    (Subgroup.centralizer_le (fun x hx => hx.1))
  have hK1 := (hAC G n J B₀ S.hn S.hq S.hyp.model S.hB0).1
  have hkle : M.relIndex D ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hDH (l14_relIndex_ne_zero _ _)).trans hK1
  have hcommBC : ∀ u ∈ B₀, ∀ c ∈ C₀, u * c = c * u := fun u hu c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2 u hu.2
  have hB₀D : B₀ ≤ D := inf_le_left.trans S.B_le_cenS_B
  have hC₀D : C₀ ≤ D := S.C0_le_cenB
  have hY : B₀ ⊔ C₀ = M ⊓ D := by
    apply le_antisymm
    · exact sup_le (le_inf le_sup_left hB₀D) (le_inf (fun c hc => Subgroup.mem_sup_right hc.2) hC₀D)
    · rintro y ⟨hyM, hyD⟩
      obtain ⟨u, hu, c, hc, rfl⟩ := l14_mem_sup_of_comm (A := B₀) (H := CenS J)
        (fun a ha h hh => Subgroup.mem_centralizer_iff.mp hh a ha.2) hyM
      have hcC : c ∈ C₀ := by
        refine ⟨?_, hc⟩
        have h1 : u⁻¹ * (u * c) ∈ Cen b :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.B_le_cen hu.1)) (S.cenB_le_cen hyD)
        simpa using h1
      exact Subgroup.mul_mem_sup hu hcC
  have hk : (B₀ ⊔ C₀).relIndex D = M.relIndex D := by
    rw [hY, Subgroup.inf_relIndex_right]
  have hYD : B₀ ⊔ C₀ ≤ D := sup_le hB₀D hC₀D
  have hXD : X ≤ D := (S.X_le_C0 hX).trans hC₀D
  have hcardY : Nat.card ↥(B₀ ⊔ C₀) = 27 * Nat.card X := by
    obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₀ C₀ hcommBC
    have h1 : Nat.card ↥(B₀ ⊓ C₀) = 1 := by
      have d1 : Nat.card ↥(B₀ ⊓ C₀) ∣ 3 ^ 2 := by
        rw [← S.e9.2]; exact Subgroup.card_dvd_of_le inf_le_left
      have d2 : Nat.card ↥(B₀ ⊓ C₀) ∣ Nat.card ↥(Subgroup.center ↥J) :=
        (Subgroup.card_dvd_of_le
          (inf_le_inf (inf_le_right : B₀ ≤ J) (inf_le_right : C₀ ≤ CenS J))).trans
          S.inf_cenS_card_dvd
      exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left 2 S.hZ3) d1 d2
    rw [h1, mul_one, S.e9.2, S.card_C0 hX] at hprod
    rw [hprod]
    ring
  have hk1 : (B₀ ⊔ C₀).relIndex D * Nat.card ↥(B₀ ⊔ C₀) = Nat.card D := by
    have := Subgroup.relIndex_mul_card (B₀ ⊔ C₀) D
    rwa [inf_of_le_left hYD] at this
  have hk2 : X.relIndex D * Nat.card X = Nat.card D := by
    have := Subgroup.relIndex_mul_card X D
    rwa [inf_of_le_left hXD] at this
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hkpos : 0 < M.relIndex D := Nat.pos_of_ne_zero (l14_relIndex_ne_zero _ _)
  have hk1' : M.relIndex D * (27 * Nat.card X) = Nat.card D := by
    rw [← hk, ← hcardY]; exact hk1
  refine ⟨M.relIndex D, by omega, ?_, ?_, ?_⟩
  · have : X.relIndex D * Nat.card X = (27 * M.relIndex D) * Nat.card X := by
      rw [hk2, ← hk1']; ring
    exact Nat.eq_of_mul_eq_mul_right hXpos this
  · rw [← hk1']; ring
  · intro h1
    have h2 : (B₀ ⊔ C₀).relIndex D = 1 := by rw [hk]; exact h1
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hYD

theorem cen_le_cenS_zpowers : Cen b ≤ CenS (Subgroup.zpowers b) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((show Commute b c from l14_cen_comm hc).zpow_left i).eq

theorem cen_inf_cenS_B₀_le : Cen b ⊓ CenS (B ⊓ J) ≤ CenS B := by
  intro c hc
  rw [← S.hsup]
  exact l14_mem_cenS_sup (S.cen_le_cenS_zpowers hc.1) hc.2

theorem XleD (hX : Odd (Nat.card (Opp 3 (Cen b)))) : Opp 3 (Cen b) ≤ CenS B :=
  (S.X_le_C0 hX).trans S.C0_le_cenB

theorem part1 (hX : Odd (Nat.card (Opp 3 (Cen b)))) (hAC : FF79KAutCentP) :
    Opp 3 (Cen b) ≤ CenS B ∧ ((Opp 3 (Cen b)).subgroupOf (CenS B)).Normal ∧
      Nat.Coprime (Nat.card (Opp 3 (Cen b))) 6 ∧
      Nat.Coprime ((Opp 3 (Cen b)).relIndex (CenS B)) (Nat.card (Opp 3 (Cen b))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hrel, -, -⟩ := S.index_data hX hAC
  have hc3 : Nat.Coprime 3 (Nat.card (Opp 3 (Cen b))) := Opp_coprime 3 _
  have hc2 : Nat.Coprime 2 (Nat.card (Opp 3 (Cen b))) := Nat.coprime_two_left.mpr hX
  refine ⟨S.XleD hX, ⟨fun x hx d => ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using Opp_conj_mem (S.cenB_le_cen d.2) hx
  · exact Nat.Coprime.mul_right hc2.symm hc3.symm
  · rw [hrel]
    have h27 : Nat.Coprime 27 (Nat.card (Opp 3 (Cen b))) := Nat.Coprime.pow_left 3 hc3
    rcases hk with rfl | rfl
    · simpa using h27
    · exact Nat.Coprime.mul_left h27 hc2

theorem cen_decomp (hX : Odd (Nat.card (Opp 3 (Cen b)))) (hAC : FF79KAutCentP)
    (hD : CenS B = (B ⊓ J) ⊔ (Cen b ⊓ CenS J)) :
    ∀ c ∈ Cen b, ∃ j ∈ J, ∃ c₀ ∈ Cen b ⊓ CenS J, c = j * c₀ := by
  intro c hc
  obtain ⟨j, hj, hjc⟩ := (hAC G n J (B ⊓ J) S.hn S.hq S.hyp.model S.hB0).2 c
    (S.cen_le_nor hc)
  have hh : j⁻¹ * c ∈ CenS B :=
    S.cen_inf_cenS_B₀_le ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.J_le_cen hj)) hc, hjc⟩
  rw [hD] at hh
  obtain ⟨u, hu, c₀, hc₀, huc⟩ := l14_mem_sup_of_comm (A := B ⊓ J) (H := Cen b ⊓ CenS J)
    (fun a ha h hh => Subgroup.mem_centralizer_iff.mp hh.2 a ha.2) hh
  refine ⟨j * u, J.mul_mem hj hu.2, c₀, hc₀, ?_⟩
  calc c = j * (j⁻¹ * c) := by group
    _ = j * (u * c₀) := by rw [huc]
    _ = j * u * c₀ := by group

theorem part3 (hX : Odd (Nat.card (Opp 3 (Cen b)))) (hAC : FF79KAutCentP) :
    (setMul3 (Subgroup.zpowers b) J (Opp 3 (Cen b)) = Cen b ∧
        Nat.card ↥(Cen b) = 3 * Nat.card ↥J * Nat.card ↥(Opp 3 (Cen b))) ∨
      Even (Nat.card ↥(CenS B)) := by
  by_cases hev : Even (Nat.card ↥(CenS B))
  · exact Or.inr hev
  refine Or.inl ?_
  obtain ⟨k, hk, -, hcardD, hk1⟩ := S.index_data hX hAC
  have hk' : k = 1 := by
    rcases hk with h | h
    · exact h
    · exfalso
      apply hev
      rw [hcardD, h]
      exact ⟨27 * Nat.card (Opp 3 (Cen b)), by ring⟩
  have hD := hk1 hk'
  have hdec := S.cen_decomp hX hAC hD
  constructor
  · refine Set.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨h, hh, k, hk, m, hm, rfl⟩ := hc
      show h * k * m ∈ Cen b
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr
        (show b ∈ Cen b from Subgroup.mem_centralizer_singleton_iff.mpr rfl) hh)
        (S.J_le_cen hk)) (Opp_le 3 _ hm)
    · have hc' : c ∈ Cen b := hc
      obtain ⟨j, hj, c₀, hc₀, rfl⟩ := hdec c hc'
      obtain ⟨i, x, hx, rfl⟩ := S.C0_decomp c₀ hc₀
      have hcomm : (j : G) * b ^ i = b ^ i * j :=
        ((show Commute b j from l14_cen_comm (S.J_le_cen hj)).symm.zpow_right i).eq
      exact ⟨b ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i, j, hj, x, hx, by
        rw [mul_assoc, ← mul_assoc j, hcomm]; group⟩
  · have hcomm : ∀ x ∈ J, ∀ y ∈ Cen b ⊓ CenS J, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp hy.2 x hx
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J (Cen b ⊓ CenS J) hcomm
    have hsup : J ⊔ (Cen b ⊓ CenS J) = Cen b := by
      apply le_antisymm
      · exact sup_le S.J_le_cen inf_le_left
      · intro c hc
        obtain ⟨j, hj, c₀, hc₀, rfl⟩ := hdec c hc
        exact Subgroup.mul_mem_sup hj hc₀
    have hinf : Nat.card ↥(J ⊓ (Cen b ⊓ CenS J)) = 1 := by
      have d1 : Nat.card ↥(J ⊓ (Cen b ⊓ CenS J)) ∣ Nat.card ↥(Subgroup.center ↥J) :=
        (Subgroup.card_dvd_of_le (inf_le_inf_left J (inf_le_right : Cen b ⊓ CenS J ≤ CenS J))).trans
          S.inf_cenS_card_dvd
      have d2 : Nat.card ↥(J ⊓ (Cen b ⊓ CenS J)) ∣ Nat.card ↥(Cen b ⊓ CenS J) :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [S.card_C0 hX] at d2
      have hodd : Odd (Nat.card ↥(J ⊓ (Cen b ⊓ CenS J))) :=
        (((by decide : Odd 3).mul hX)).of_dvd_nat d2
      rcases (Nat.dvd_prime Nat.prime_two).mp (d1.trans S.hZ) with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [hsup, hinf, mul_one, S.card_C0 hX] at h1
    rw [h1]
    ring

theorem relIndex_C0 (hX : Odd (Nat.card (Opp 3 (Cen b)))) :
    (Opp 3 (Cen b)).relIndex (Cen b ⊓ CenS J) = 3 := by
  have h := Subgroup.relIndex_mul_card (Opp 3 (Cen b)) (Cen b ⊓ CenS J)
  rw [inf_of_le_left (S.X_le_C0 hX), S.card_C0 hX] at h
  have hpos : 0 < Nat.card (Opp 3 (Cen b)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h

theorem opp_cenS_of_mem (hX : Odd (Nat.card (Opp 3 (Cen b)))) (hAC : FF79KAutCentP)
    (hCA : FF79KCentAlpha) (hodd : Odd (Nat.card ↥(CenS B)) ∨ n = 5) {A : Subgroup G}
    (hAB : A ≤ B) (hbA : b ∈ A) (hne : A ≠ B) : Opp 3 (CenS A) = Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcen : CenS A ≤ Cen b := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  apply le_antisymm
  swap
  · refine le_Opp_of_normalized ((S.XleD hX).trans (Subgroup.centralizer_le hAB))
      (fun h hh x hx => Opp_conj_mem (hAcen hh) hx) (Opp_coprime 3 _)
  have hzA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hbA
  by_cases hA : A ≤ Subgroup.zpowers b
  · have hAeq : A = Subgroup.zpowers b := le_antisymm hA hzA
    have : CenS A = Cen b := le_antisymm hAcen (by rw [hAeq]; exact S.cen_le_cenS_zpowers)
    rw [this]
  obtain ⟨a, haA, haz⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers b := by
    by_contra hcon
    apply hA
    intro a ha
    by_contra hna
    exact hcon ⟨a, ha, hna⟩
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr S.b_mem_B
  have hBdec : ∀ a ∈ B, ∃ z ∈ Subgroup.zpowers b, ∃ u ∈ B ⊓ J, a = z * u := by
    intro a ha
    rw [← S.hsup] at ha
    exact l14_mem_sup_of_comm (A := Subgroup.zpowers b) (H := B ⊓ J)
      (fun x hx y hy => S.B_comm x (hzB hx) y hy.1) ha
  obtain ⟨z, hz, α, hα, hazα⟩ := hBdec a (hAB haA)
  have hαA : α ∈ A := by
    have h1 : z⁻¹ * a ∈ A := A.mul_mem (A.inv_mem (hzA hz)) haA
    rw [hazα, inv_mul_cancel_left] at h1
    exact h1
  have hα1 : α ≠ 1 := by
    intro h1
    apply haz
    rw [hazα, h1, mul_one]
    exact hz
  haveI : IsElementaryAbelian 3 ↥(B ⊓ J) := S.e9.1
  have hα3 : α ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B ⊓ J) α hα
  have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hA₀ : A ⊓ (B ⊓ J) = Subgroup.zpowers α := by
    have hle : Subgroup.zpowers α ≤ A ⊓ (B ⊓ J) :=
      Subgroup.zpowers_le.mpr ⟨hαA, hα⟩
    have hdvd : Nat.card ↥(A ⊓ (B ⊓ J)) ∣ 3 ^ 2 := by
      rw [← S.e9.2]; exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne9 : A ⊓ (B ⊓ J) ≠ B ⊓ J := by
      intro h
      apply hne
      have hB₀A : B ⊓ J ≤ A := h ▸ inf_le_left
      apply le_antisymm hAB
      rw [← S.hsup]
      exact sup_le hzA hB₀A
    have hi2 : i ≠ 2 := by
      rintro rfl
      apply hne9
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [S.e9.2, hci]
    have hi0 : i ≠ 0 := by
      rintro rfl
      have h1 : (A ⊓ (B ⊓ J)) = ⊥ := (Subgroup.eq_bot_iff_card _).mpr (by simpa using hci)
      have : α ∈ A ⊓ (B ⊓ J) := ⟨hαA, hα⟩
      rw [h1, Subgroup.mem_bot] at this
      exact hα1 this
    have hi1 : i = 1 := by omega
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hci, hi1, Nat.card_zpowers, hαo]
    norm_num
  have hAdec : ∀ x ∈ A, ∃ z ∈ Subgroup.zpowers b, ∃ u ∈ Subgroup.zpowers α, x = z * u := by
    intro x hx
    obtain ⟨z', hz', u, hu, rfl⟩ := hBdec x (hAB hx)
    refine ⟨z', hz', u, ?_, rfl⟩
    rw [← hA₀]
    have h1 : z'⁻¹ * (z' * u) ∈ A := A.mul_mem (A.inv_mem (hzA hz')) hx
    rw [inv_mul_cancel_left] at h1
    exact ⟨h1, hu⟩
  have hjA : ∀ j ∈ J ⊓ Cen α, j ∈ CenS A := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨z', hz', u, hu, rfl⟩ := hAdec x hx
    have h1 : Commute (z' : G) j := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ((show Commute b j from l14_cen_comm (S.J_le_cen hj.1)).zpow_left i)
    have h2 : Commute (u : G) j := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((show Commute α j from l14_cen_comm hj.2).zpow_left i)
    exact (h1.mul_left h2).eq
  have hYle : Opp 3 (CenS A) ≤ CenS A := Opp_le 3 _
  obtain ⟨hYP, hY5⟩ := hCA G n J (B ⊓ J) S.hn S.hq S.hyp.model S.hB0 α hα hαo (Opp 3 (CenS A))
    (hYle.trans (hAcen.trans S.cen_le_nor))
    (hYle.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hαA)))
    (Opp_coprime 3 _) (fun j hj y hy => Opp_conj_mem (hjA j hj) hy)
  have hXD := S.XleD hX
  rcases S.hn with h4 | h5
  ·
    have hodd' : Odd (Nat.card ↥(CenS B)) := hodd.resolve_right (by omega)
    obtain ⟨k, hk, hrel, -, -⟩ := S.index_data hX hAC
    have hYD : Opp 3 (CenS A) ≤ CenS B :=
      fun y hy => S.cen_inf_cenS_B₀_le ⟨hAcen (hYle hy), hYP hy⟩
    refine le_of_coprime_relIndex hXD (fun d hd x hx => Opp_conj_mem (S.cenB_le_cen hd) hx)
      hYD ?_
    have hYodd : Odd (Nat.card ↥(Opp 3 (CenS A))) :=
      hodd'.of_dvd_nat (Subgroup.card_dvd_of_le hYD)
    have hc3 : Nat.Coprime (Nat.card ↥(Opp 3 (CenS A))) 3 := (Opp_coprime 3 _).symm
    have hc2 : Nat.Coprime (Nat.card ↥(Opp 3 (CenS A))) 2 := (Nat.coprime_two_left.mpr hYodd).symm
    rw [hrel]
    have h27 : Nat.Coprime (Nat.card ↥(Opp 3 (CenS A))) 27 := Nat.Coprime.pow_right 3 hc3
    rcases hk with rfl | rfl
    · simpa using h27
    · exact Nat.Coprime.mul_right h27 hc2
  ·
    have hYC : Opp 3 (CenS A) ≤ Cen b ⊓ CenS J := fun y hy => ⟨hAcen (hYle hy), hY5 h5 hy⟩
    refine le_of_coprime_relIndex (S.X_le_C0 hX) (fun d hd x hx => Opp_conj_mem hd.1 hx) hYC ?_
    rw [S.relIndex_C0 hX]
    exact (Opp_coprime 3 _).symm

end Setup14

private theorem l14_conjBy_cenS (g : G) (H : Subgroup G) :
    CenS (conjBy g H) = conjBy g (CenS H) := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    show g⁻¹ * z * g ∈ CenS H
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_centralizer_iff.mp hz (g * h * g⁻¹) ⟨h, hh, by simp⟩
    calc h * (g⁻¹ * z * g) = g⁻¹ * ((g * h * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * h * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * z * g * h := by group
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * c * g⁻¹) = g * (h * c) * g⁻¹ := by group
      _ = g * (c * h) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * (g * h * g⁻¹) := by group

private theorem l14_conjBy_inv_conjBy (g : G) (H : Subgroup G) : conjBy g (conjBy g⁻¹ H) = H := by
  have := conjBy_conjBy_inv g⁻¹ H
  rwa [inv_inv] at this

theorem ff79_1_4_of (hK : FF79KTypeLn) (h14k : FF79KCenterJ ∧ FF79KAutCentP ∧
    FF79KCentAlpha) : FF79_1_4 := by
  obtain ⟨hCJ, hAC, hCA⟩ := h14k
  intro G _ _ n hn b J h B hB hX hCB X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have S := setup14 hK hCJ hn h hB
  obtain ⟨p1, p2, p3, p4⟩ := S.part1 hX hAC
  refine ⟨p1, p2, p3, p4, ?_, S.part3 hX hAC⟩
  intro A hAB hconj
  obtain ⟨g, hg⟩ := hconj
  have haB : g * b * g⁻¹ ∈ B := hAB.le hg
  set B' : Subgroup G := conjBy g⁻¹ B with hB'
  set A' : Subgroup G := conjBy g⁻¹ A with hA'
  have hB'le : B' ≤ Cen b := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    apply l14_mem_cen
    have := S.B_comm _ haB y hy
    calc b * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * ((g * b * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * b * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g⁻¹⁻¹ * b := by group
  have hcardB' : Nat.card ↥B' = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'syl : IsSylowOf 3 B' (Cen b) :=
    isSylowOf_of_card hB'le (by rw [hcardB']; exact isSylowOf_card hB)
  have S' := setup14 hK hCJ hn h hB'syl
  have hcenB' : CenS B' = conjBy g⁻¹ (CenS B) := by
    rw [hB', l14_conjBy_cenS]
  have hodd' : Odd (Nat.card ↥(CenS B')) ∨ n = 5 := by
    rw [hcenB', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hCB
  have hA'B' : A' ≤ B' := Subgroup.map_mono hAB.le
  have hbA' : b ∈ A' := ⟨g * b * g⁻¹, hg, by simp [MulAut.conj_apply]; group⟩
  have hne : A' ≠ B' := by
    intro heq
    have := congrArg (conjBy g) heq
    rw [hA', hB', l14_conjBy_inv_conjBy, l14_conjBy_inv_conjBy] at this
    exact hAB.ne this
  have key := S'.opp_cenS_of_mem hX hAC hCA hodd' hA'B' hbA' hne
  have hcenA' : CenS A' = conjBy g⁻¹ (CenS A) := by
    rw [hA', l14_conjBy_cenS]
  rw [hcenA', ← conjBy_Opp] at key
  have hOpp : Opp 3 (CenS A) = conjBy g (Opp 3 (Cen b)) := by
    rw [← key, l14_conjBy_inv_conjBy]
  rw [hOpp]
  obtain ⟨q1, -, -, q4⟩ := S'.part1 hX hAC
  have hXg : conjBy g X ≤ CenS B := by
    have : conjBy g X ≤ conjBy g (CenS B') := Subgroup.map_mono q1
    rwa [hcenB', l14_conjBy_inv_conjBy] at this
  have hcardX : Nat.card ↥(conjBy g X) = Nat.card ↥X :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle : conjBy g X ≤ X :=
    le_of_coprime_relIndex p1 (fun d hd x hx => Opp_conj_mem (S.cenB_le_cen hd) hx) hXg
      (by rw [hcardX]; exact p4.symm)
  exact Subgroup.eq_of_le_of_card_ge hle hcardX.ge

end CFSG.RankThree.PartTwo.Sec21.FF79
