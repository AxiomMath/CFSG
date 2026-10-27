module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofTrans
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem card_comap_mk_theta (K : Subgroup (G ⧸ aschbacherSolvableCore 3 G)) :
    Nat.card (K.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) =
      Nat.card K * Nat.card (aschbacherSolvableCore 3 G) := by
  set θ := aschbacherSolvableCore 3 G
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' θ))
  have h2 : (K.comap (QuotientGroup.mk' θ)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective θ)
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [h2] at h1
  have h5 : Nat.card (K.comap (QuotientGroup.mk' θ)) * K.index =
      (Nat.card K * Nat.card θ) * K.index := by
    rw [h1, h4, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem exists_normalizer_lift_theta {A : Subgroup G} (hA : IsPGroup 3 A) {n : G}
    (hy : QuotientGroup.mk' (aschbacherSolvableCore 3 G) n ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G))) :
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      ∃ e ∈ A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
        QuotientGroup.mk' (aschbacherSolvableCore 3 G) n =
          e * QuotientGroup.mk' (aschbacherSolvableCore 3 G) w := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set θ := aschbacherSolvableCore 3 G with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ē : Subgroup (G ⧸ θ) := A.map π with hĒ
  set Ph : Subgroup G := Ē.comap π with hPh
  have hAPh : A ≤ Ph := fun x hx => Subgroup.mem_map_of_mem _ hx
  set S₂ : Subgroup G := A.map (MulAut.conj n).toMonoidHom with hS₂
  have hnorm := Subgroup.mem_normalizer_iff.1 hy
  have hS₂Ph : S₂ ≤ Ph := by
    rintro _ ⟨z, hz, rfl⟩
    show π (n * z * n⁻¹) ∈ Ē
    rw [map_mul, map_mul, map_inv]
    exact (hnorm (π z)).1 (Subgroup.mem_map_of_mem _ hz)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcardĒ : Nat.card Ē = Nat.card A :=
    card_map_of_injOn π (injOn_mk_of_isPGroup hp hA)
  have hcardPh : Nat.card Ph = 3 ^ k * Nat.card θ := by
    rw [hPh, card_comap_mk_theta, hcardĒ, hk]
  have hfac : (Nat.card Ph).factorization 3 = k := by
    rw [hcardPh, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        three_not_dvd_card_aschbacherSolvableCore]
    simp [hp.factorization_pow]
  have hcardS₂ : Nat.card S₂ = 3 ^ k := by
    rw [hS₂, Subgroup.card_map_of_injective (MulAut.conj n).injective, hk]
  have hA₁ : Nat.card (A.subgroupOf Ph) = 3 ^ (Nat.card ↥Ph).factorization 3 := by
    rw [hfac, ← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPh).toEquiv
  have hA₂ : Nat.card (S₂.subgroupOf Ph) = 3 ^ (Nat.card ↥Ph).factorization 3 := by
    rw [hfac, ← hcardS₂]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂Ph).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Ph) (Sylow.ofCard (S₂.subgroupOf Ph) hA₂)
    (Sylow.ofCard (A.subgroupOf Ph) hA₁)
  have hconj : ∀ z ∈ S₂, (g : G) * z * (g : G)⁻¹ ∈ A := by
    intro z hz
    have hz' : (⟨z, hS₂Ph hz⟩ : ↥Ph) ∈ S₂.subgroupOf Ph := Subgroup.mem_subgroupOf.2 hz
    have h3 : ((g • (Sylow.ofCard (S₂.subgroupOf Ph) hA₂) : Sylow 3 ↥Ph) : Subgroup ↥Ph) =
        A.subgroupOf Ph := by
      rw [hg]
      rfl
    have h2 : (g : ↥Ph) * ⟨z, hS₂Ph hz⟩ * g⁻¹ ∈ (A.subgroupOf Ph) := by
      rw [← h3, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨z, hS₂Ph hz⟩ : ↥Ph) (MulAut.conj g) _ hz'
    exact Subgroup.mem_subgroupOf.1 h2
  set w₀ : G := (g : G) * n with hw₀
  have hmap : A.map (MulAut.conj w₀).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have : w₀ * x * w₀⁻¹ = (g : G) * (n * x * n⁻¹) * (g : G)⁻¹ := by rw [hw₀]; group
    show w₀ * x * w₀⁻¹ ∈ A
    rw [this]
    exact hconj _ ⟨x, hx, rfl⟩
  have hw₀N : w₀ ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj w₀).injective])
  refine ⟨w₀, hw₀N, (π (g : G))⁻¹, Subgroup.inv_mem _ g.2, ?_⟩
  rw [hw₀, map_mul, inv_mul_cancel_left]

theorem mem_of_mk_mem_map {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) {y : G}
    (hy3 : y ^ 3 = 1)
    (hy : QuotientGroup.mk' (aschbacherSolvableCore 3 G) y ∈
      L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) : y ∈ L := by
  obtain ⟨l, hl, hly⟩ := hy
  obtain ⟨-, -, -, -, -, -, hNL, -⟩ := theta_component_quotient_structure Nat.prime_three hL
  have htN : l⁻¹ * y ∈ aschbacherSolvableCore 3 G := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l⁻¹ * y) = 1
    rw [map_mul, map_inv, hly, inv_mul_cancel]
  have hx3 : (l * (l⁻¹ * y)) ^ 3 = 1 := by rw [mul_inv_cancel_left]; exact hy3
  have htL := Item462Proof.mem_of_mul_pow_three hNL three_not_dvd_card_aschbacherSolvableCore hl
    htN hx3
  have := L.mul_mem hl htL
  rwa [mul_inv_cancel_left] at this

theorem false_of_inner {A B D L : Subgroup G} {a b : G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hBD : B ⊓ D = ⊥)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAL3 : A ⊓ L ≤ Subgroup.zpowers a)
    (hZ : ∀ z ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      (∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), z * k = k * z) →
        z ∈ (Subgroup.zpowers a).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
    {v : G ⧸ aschbacherSolvableCore 3 G}
    (hvL : v ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) (hv3 : v ^ 3 = 1)
    (hvZ : ¬ ∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), v * k = k * v)
    (hbv : ∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) b * k *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 G) b)⁻¹ = v * k * v⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 G) v
  set ρ := QuotientGroup.mk' (aschbacherSolvableCore 3 G) with hρ
  set K := L.map ρ with hK
  have hAe := hmax.1
  have hbA := hBA hbB
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hinj : Set.InjOn ρ (A : Set G) := injOn_mk_of_isPGroup Nat.prime_three hAp
  have haA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr (hBA haB)
  have hcen : ∀ y ∈ Subgroup.zpowers a, ∀ g : G ⧸ aschbacherSolvableCore 3 G,
      g * ρ y = ρ y * g := by
    intro y hy g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 G) g
    rw [← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hy) g]
  have hxK : ∀ x ∈ A, ∀ k ∈ K, ρ x * k * (ρ x)⁻¹ ∈ K := by
    rintro x hx _ ⟨l, hl, rfl⟩
    refine ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hAL hx) l).mp hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hs : ∀ x ∈ A, ∀ k ∈ K,
      (ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹) * k = k * (ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹) := by
    intro x hx k hk
    have hyb : ρ x * ρ b = ρ b * ρ x := by rw [← map_mul, ← map_mul, hcomm x hx b hbA]
    have key : ∀ k ∈ K,
        (ρ x * ρ n * (ρ x)⁻¹) * k * (ρ x * ρ n * (ρ x)⁻¹)⁻¹ = ρ n * k * (ρ n)⁻¹ := by
      intro k hk
      have hk' : (ρ x)⁻¹ * k * ρ x ∈ K := by
        have := hxK x⁻¹ (A.inv_mem hx) k hk
        rwa [map_inv, inv_inv] at this
      calc (ρ x * ρ n * (ρ x)⁻¹) * k * (ρ x * ρ n * (ρ x)⁻¹)⁻¹ =
            ρ x * (ρ n * ((ρ x)⁻¹ * k * ρ x) * (ρ n)⁻¹) * (ρ x)⁻¹ := by group
        _ = ρ x * (ρ b * ((ρ x)⁻¹ * k * ρ x) * (ρ b)⁻¹) * (ρ x)⁻¹ := by rw [hbv _ hk']
        _ = (ρ x * ρ b * (ρ x)⁻¹) * k * (ρ x * ρ b * (ρ x)⁻¹)⁻¹ := by group
        _ = ρ b * k * (ρ b)⁻¹ := by rw [hyb, mul_inv_cancel_right]
        _ = ρ n * k * (ρ n)⁻¹ := hbv k hk
    have hvk : (ρ n)⁻¹ * k * ρ n ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hvL) hk) hvL
    have h2 : (ρ x * ρ n * (ρ x)⁻¹) * ((ρ n)⁻¹ * k * ρ n) * (ρ x * ρ n * (ρ x)⁻¹)⁻¹ = k := by
      rw [key _ hvk]; group
    calc (ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹) * k =
          (ρ x * ρ n * (ρ x)⁻¹) * ((ρ n)⁻¹ * k * ρ n) * (ρ x * ρ n * (ρ x)⁻¹)⁻¹ *
            (ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹) := by group
      _ = k * (ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹) := by rw [h2]
  have hsa : ∀ x ∈ A, ρ x * ρ n * (ρ x)⁻¹ * (ρ n)⁻¹ ∈ (Subgroup.zpowers a).map ρ := fun x hx =>
    hZ _ (K.mul_mem (hxK x hx (ρ n) hvL) (K.inv_mem hvL)) (hs x hx)
  have hvN : ρ n ∈ Subgroup.normalizer ((A.map ρ : Subgroup (G ⧸ aschbacherSolvableCore 3 G)) :
      Set (G ⧸ aschbacherSolvableCore 3 G)) := by
    have hle : (A.map ρ).map (MulAut.conj (ρ n)⁻¹).toMonoidHom ≤ A.map ρ := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨y, hy, hys⟩ := hsa x hx
      refine ⟨y * x, A.mul_mem (haA hy) hx, ?_⟩
      have hXv : ρ x * ρ n * (ρ x)⁻¹ = ρ y * ρ n := by rw [hys]; group
      have hsv : ρ y * ρ n = ρ n * ρ y := (hcen y hy (ρ n)).symm
      change ρ (y * x) = (ρ n)⁻¹ * ρ x * (ρ n)⁻¹⁻¹
      rw [inv_inv, map_mul]
      calc ρ y * ρ x = (ρ n)⁻¹ * (ρ n * ρ y) * ρ x := by group
        _ = (ρ n)⁻¹ * (ρ y * ρ n) * ρ x := by rw [hsv]
        _ = (ρ n)⁻¹ * (ρ x * ρ n * (ρ x)⁻¹) * ρ x := by rw [hXv]
        _ = (ρ n)⁻¹ * ρ x * ρ n := by group
    have hv' : (ρ n)⁻¹ ∈ Subgroup.normalizer
        ((A.map ρ : Subgroup (G ⧸ aschbacherSolvableCore 3 G)) :
          Set (G ⧸ aschbacherSolvableCore 3 G)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (ρ n)⁻¹).injective).ge
    simpa using Subgroup.inv_mem _ hv'
  obtain ⟨w, hwN, e, he, hnwe⟩ := exists_normalizer_lift_theta hAp hvN
  obtain ⟨x₀, hx₀, rfl⟩ := he
  have hD : ∀ d ∈ D, ρ d * ρ n = ρ n * ρ d := by
    intro d hd
    have hdA := hDA hd
    have hwd : w * d * w⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hND hwN) d).mp hd
    have htD : w * d * w⁻¹ * d⁻¹ ∈ D := D.mul_mem hwd (D.inv_mem hd)
    obtain ⟨y, hy, hys⟩ := hsa d hdA
    have hw : ρ w = (ρ x₀)⁻¹ * ρ n := by rw [hnwe, inv_mul_cancel_left]
    have hx₀d : ρ x₀ * ρ d = ρ d * ρ x₀ := by rw [← map_mul, ← map_mul, hcomm x₀ hx₀ d hdA]
    have e1 : ρ n * ρ d * (ρ n)⁻¹ = (ρ y)⁻¹ * ρ d := by rw [hys]; group
    have e2 : (ρ x₀)⁻¹ * (ρ y)⁻¹ = (ρ y)⁻¹ * (ρ x₀)⁻¹ :=
      (Commute.inv_inv (hcen y hy (ρ x₀))).eq
    have e3 : (ρ x₀)⁻¹ * ρ d * ρ x₀ = ρ d := by rw [mul_assoc, ← hx₀d, inv_mul_cancel_left]
    have hρt : ρ (w * d * w⁻¹ * d⁻¹) = (ρ y)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hw]
      calc (ρ x₀)⁻¹ * ρ n * ρ d * ((ρ x₀)⁻¹ * ρ n)⁻¹ * (ρ d)⁻¹ =
            (ρ x₀)⁻¹ * (ρ n * ρ d * (ρ n)⁻¹) * ρ x₀ * (ρ d)⁻¹ := by group
        _ = (ρ x₀)⁻¹ * ((ρ y)⁻¹ * ρ d) * ρ x₀ * (ρ d)⁻¹ := by rw [e1]
        _ = ((ρ x₀)⁻¹ * (ρ y)⁻¹) * ρ d * ρ x₀ * (ρ d)⁻¹ := by group
        _ = ((ρ y)⁻¹ * (ρ x₀)⁻¹) * ρ d * ρ x₀ * (ρ d)⁻¹ := by rw [e2]
        _ = (ρ y)⁻¹ * ((ρ x₀)⁻¹ * ρ d * ρ x₀) * (ρ d)⁻¹ := by group
        _ = (ρ y)⁻¹ * ρ d * (ρ d)⁻¹ := by rw [e3]
        _ = (ρ y)⁻¹ := mul_inv_cancel_right _ _
    have hyA : y ∈ A := haA hy
    have ht : w * d * w⁻¹ * d⁻¹ = y⁻¹ :=
      hinj (hDA htD) (A.inv_mem hyA) (by rw [hρt, map_inv])
    have ht1 : w * d * w⁻¹ * d⁻¹ = 1 := by
      have hyB : y⁻¹ ∈ B := B.inv_mem ((Subgroup.zpowers_le.mpr haB) hy)
      have : w * d * w⁻¹ * d⁻¹ ∈ B ⊓ D := ⟨ht ▸ hyB, htD⟩
      rwa [hBD, Subgroup.mem_bot] at this
    have hy1 : ρ y = 1 := by
      rw [← inv_inj, ← map_inv, ← ht, ht1, map_one, inv_one]
    rw [hy1] at hys
    calc ρ d * ρ n = (ρ d * ρ n * (ρ d)⁻¹ * (ρ n)⁻¹) * ρ n * ρ d := by group
      _ = ρ n * ρ d := by rw [← hys, one_mul]
  have hvb : ρ b * ρ n = ρ n * ρ b := by
    have := hbv (ρ n) hvL
    calc ρ b * ρ n = (ρ b * ρ n * (ρ b)⁻¹) * ρ b := by group
      _ = ρ n * ρ b := by rw [this]; group
  have hvA : ρ n ∈ Subgroup.centralizer ((A.map ρ : Subgroup (G ⧸ aschbacherSolvableCore 3 G)) :
      Set (G ⧸ aschbacherSolvableCore 3 G)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, j, d, hd, rfl⟩ :=
      exists_eq_of_mem_A hAe haZ ha3 haB hbB hba hBA hB9 hDA hBDA hx
    have h1 : Commute (ρ a) (ρ n) := (hcen a (Subgroup.mem_zpowers a) (ρ n)).symm
    have h2 : Commute (ρ b) (ρ n) := hvb
    have h3 : Commute (ρ d) (ρ n) := hD d hd
    rw [map_mul, map_mul, map_zpow, map_zpow]
    exact ((h1.zpow_left i).mul_left (h2.zpow_left j)).mul_left h3
  obtain ⟨y, hyA, hyn⟩ := Item422Proof.mem_map_of_maximal hmax (aschbacherSolvableCore 3 G)
    three_not_dvd_card_aschbacherSolvableCore hv3 hvA
  have hyL : y ∈ L := mem_of_mk_mem_map hL (hAe.2 y hyA) (by rw [hyn]; exact hvL)
  have hya : y ∈ Subgroup.zpowers a := hAL3 ⟨hyA, hyL⟩
  apply hvZ
  intro k _
  rw [← hyn]
  exact (hcen y hya k).symm

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
