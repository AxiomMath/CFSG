module

public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofGen
import CFSG.LieType.SeitzGeneration.NonabHeisThree
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofHess
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Proof1513Res3

theorem map_closure_centralizers {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (D : Subgroup X) :
    (Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k}).map φ.toMonoidHom =
      Subgroup.closure {k : Y | ∃ x ∈ D.map φ.toMonoidHom, x ≠ 1 ∧ k * x = x * k} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext k
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨k', ⟨x, hxD, hx1, hkx⟩, rfl⟩
    refine ⟨φ x, ⟨x, hxD, rfl⟩, ?_, ?_⟩
    · intro h
      apply hx1
      have := congrArg φ.symm h
      simpa using this
    · change φ k' * φ x = φ x * φ k'
      rw [← map_mul, hkx, map_mul]
  · rintro ⟨_, ⟨x, hxD, rfl⟩, hx1, hkx⟩
    refine ⟨φ.symm k, ⟨x, hxD, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hkx

theorem closure_centralizers_eq_top_linear {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hq1 : p ^ e % 3 = 1)
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p e)) (h4 : 4 < p ^ e)
    (D : Subgroup X) (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  set F := GaloisField p e
  have hF : Nat.card F = p ^ e := GaloisField.card p e (by omega)
  set ψ : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    φ.trans (Sec4.Census.pslEquivProjSL 3 F).symm with hψ
  have hψinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have hgen := CFSG.LieType.SeitzGeneration.closure_centralizers_psl_three (F := F) (n := 3)
    (by rw [hF]; omega) (dvd_refl 3) (by norm_num) (fun _ => by rw [hF]; exact h4)
    (D.map ψ.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      change ψ x * ψ y = ψ y * ψ x
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)))
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ψ x ^ 3 = 1
      rw [← map_pow, hD.2 x hx, map_one])
    (by rw [Subgroup.card_map_of_injective hψinj, hD9]; norm_num)
  rw [← map_closure_centralizers ψ D] at hgen
  rw [eq_top_iff]
  intro k _
  have hk : ψ.toMonoidHom k ∈
      (Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k}).map ψ.toMonoidHom := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_map_iff_mem hψinj).mp hk

section Model

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mul_comm_of_mem_statedScalars {w : GL (Fin 3) K} (hw : w ∈ StatedScalars (Fin 3) K)
    (g : GL (Fin 3) K) : g * w = w * g := by
  obtain ⟨u, rfl⟩ := hw
  exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq

theorem not_nine_dvd_card_sub_one' (hK : PiField π p f K)
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) : ¬ 9 ∣ Nat.card K - 1 := by
  rw [hK.card]
  have hr : p ^ f % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  cases π
  · change ¬ 9 ∣ (p ^ f) ^ 2 - 1
    intro hd
    have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1 : (p ^ f) ^ 2 % 9 = 1 := by omega
    rw [Nat.pow_mod] at h1
    have key : ∀ r < 9, r ^ 2 % 9 = 1 → r = 1 ∨ r = 8 := by decide
    exact h9 (key _ hr h1)
  · change ¬ 9 ∣ p ^ f - 1
    intro hd
    exact h9 (Or.inl (by omega))

theorem not_dvd_card_of_equiv {X : Type} [Group X] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8))
    (φ : X ≃* projImage (slPi π 3 (p ^ f) K)) : ¬ 27 ∣ Nat.card X := by
  rw [Nat.card_congr φ.toEquiv]
  exact KSL3Two.not_dvd_card_projImage hK hq h9

theorem mem_of_isPGroup_normalizer {X : Type} [Group X] [Finite X] (h27 : ¬ 27 ∣ Nat.card X)
    {D : Subgroup X} (hD9 : Nat.card D = 9) {h : X} {a : ℕ} (hh : h ^ 3 ^ a = 1)
    (hhD : h ∈ Subgroup.normalizer (D : Set X)) : h ∈ D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD9]; norm_num)
  have hh3 : IsPGroup 3 (Subgroup.zpowers h) := by
    have hd : orderOf h ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hh
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hP : IsPGroup 3 (D ⊔ Subgroup.zpowers h : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hD3 hh3 (Subgroup.zpowers_le.mpr hhD)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  by_contra hhD'
  have hDP : D ≤ D ⊔ Subgroup.zpowers h := le_sup_left
  have h9P : 9 ∣ Nat.card (D ⊔ Subgroup.zpowers h : Subgroup X) :=
    hD9 ▸ Subgroup.card_dvd_of_le hDP
  have hne : Nat.card (D ⊔ Subgroup.zpowers h : Subgroup X) ≠ 9 := by
    intro h9
    have hEq : D = D ⊔ Subgroup.zpowers h :=
      Subgroup.eq_of_le_of_card_ge hDP (by rw [h9, hD9])
    exact hhD' (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers h))
  have h27P : 27 ∣ Nat.card (D ⊔ Subgroup.zpowers h : Subgroup X) := by
    rw [hk] at h9P hne ⊢
    rcases k with _ | _ | _ | k
    · norm_num at h9P
    · norm_num at h9P
    · norm_num at hne
    · exact ⟨3 ^ k, by ring⟩
  exact h27 (h27P.trans (Subgroup.card_subgroup_dvd_card _))

theorem mem_centralizer_of_mem_normalizer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) {X : Type} [Group X] [Finite X]
    (φ : X ≃* projImage (slPi π 3 (p ^ f) K))
    {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    {x : X} (hxD : x ∈ D) (hx1 : x ≠ 1) {g : X} (hgx : g * x = x * g)
    (hgD : g ∈ Subgroup.normalizer (D : Set X)) : g ∈ Subgroup.centralizer (D : Set X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9K := not_nine_dvd_card_sub_one' hK h9
  have h27 := not_dvd_card_of_equiv hK hq h9 φ
  set S := projImage (slPi π 3 (p ^ f) K) with hS
  set ψ : X →* ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψS : ∀ z : X, ψ z ∈ S := fun z => (φ z).2
  set E := D.map ψ with hE
  have hEa : CFSG.Assembly.IsElemAbelian 3 E := CFSG.SectionRank.isElemAbelian_map hD ψ
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hx3 : x ^ 3 = 1 := hD.2 x hxD
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have : Finite (Subgroup.zpowers x) := inferInstance
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from hall)
    rw [Nat.card_zpowers, hD9, hxo] at hle
    omega
  obtain ⟨xh, hxhS, hxh⟩ := hψS x
  obtain ⟨yh, hyhS, hyh⟩ := hψS y
  obtain ⟨gh, hghS, hgh⟩ := hψS g
  have hmkE : ∀ z ∈ D, ψ z ∈ E := fun z hz => ⟨z, hz, rfl⟩
  have hψx1 : ψ x ≠ 1 := fun h => hx1 (hψinj (h.trans (map_one ψ).symm))
  have hnot_mem : ∀ z : X, z ∉ Subgroup.zpowers x → ψ z ∉ Subgroup.zpowers (ψ x) := by
    intro z hz hψz
    rw [← MonoidHom.map_zpowers] at hψz
    exact hz ((Subgroup.mem_map_iff_mem hψinj).mp hψz)
  set c := xh * yh * xh⁻¹ * yh⁻¹ with hc
  have hcS : c ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', hc, map_mul, map_mul, map_mul, map_inv,
      map_inv, hxh, hyh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      hcommD x hxD y hyD]
    simp
  set l := gh * xh * gh⁻¹ * xh⁻¹ with hl
  have hlS : l ∈ StatedScalars (Fin 3) K := by
    rw [← KFacts.mk_eq_one_iff_mem_statedScalars', hl, map_mul, map_mul, map_mul, map_inv,
      map_inv, hgh, hxh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hgx]
    simp
  have hcc := mul_comm_of_mem_statedScalars hcS
  have hlc := mul_comm_of_mem_statedScalars hlS
  have hwD : g * y * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD y).mp hyD
  set wh := gh * yh * gh⁻¹ with hwh
  have hwhS : wh ∈ slPi π 3 (p ^ f) K := mul_mem (mul_mem hghS hyhS) (inv_mem hghS)
  have hmkwh : ProjGenLinGroup.mk wh = ψ (g * y * g⁻¹) := by
    rw [hwh, map_mul, map_mul, map_inv, hgh, hyh, map_mul, map_mul, map_inv]
  have hxwh : xh * wh * xh⁻¹ * wh⁻¹ = c := by
    have e1 : gh * xh * gh⁻¹ = l * xh := by rw [hl]; group
    have e2 : gh * c * gh⁻¹ = c := by rw [hcc gh]; group
    have e3 : gh * c * gh⁻¹ = (gh * xh * gh⁻¹) * wh * (gh * xh * gh⁻¹)⁻¹ * wh⁻¹ := by
      rw [hc, hwh]; group
    rw [e1, e2] at e3
    rw [e3]
    calc xh * wh * xh⁻¹ * wh⁻¹ = (xh * wh * xh⁻¹) * l * l⁻¹ * wh⁻¹ := by group
      _ = l * (xh * wh * xh⁻¹) * l⁻¹ * wh⁻¹ := by rw [hlc (xh * wh * xh⁻¹)]
      _ = l * xh * wh * (l * xh)⁻¹ * wh⁻¹ := by group
  have hcomm : xh * (wh * yh⁻¹) = (wh * yh⁻¹) * xh := by
    have e1 : xh * wh = c * (wh * xh) := by rw [← hxwh]; group
    have e2 : xh * yh⁻¹ = c⁻¹ * (yh⁻¹ * xh) := by
      have : xh * yh = c * (yh * xh) := by rw [hc]; group
      calc xh * yh⁻¹ = yh⁻¹ * (yh * xh) * yh⁻¹ := by group
        _ = yh⁻¹ * (c⁻¹ * (xh * yh)) * yh⁻¹ := by rw [this]; group
        _ = c⁻¹ * yh⁻¹ * (xh * yh) * yh⁻¹ := by
          rw [← mul_assoc yh⁻¹ c⁻¹, (mul_comm_of_mem_statedScalars (inv_mem hcS)) yh⁻¹]
        _ = c⁻¹ * (yh⁻¹ * xh) := by group
    calc xh * (wh * yh⁻¹) = (xh * wh) * yh⁻¹ := by group
      _ = c * (wh * xh) * yh⁻¹ := by rw [e1]
      _ = c * wh * (xh * yh⁻¹) := by group
      _ = c * wh * (c⁻¹ * (yh⁻¹ * xh)) := by rw [e2]
      _ = c * (wh * c⁻¹) * (yh⁻¹ * xh) := by group
      _ = c * (c⁻¹ * wh) * (yh⁻¹ * xh) := by
          rw [(mul_comm_of_mem_statedScalars (inv_mem hcS)) wh]
      _ = (wh * yh⁻¹) * xh := by group
  have hwy : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x := by
    by_contra hnot
    refine KSL3Two.lifts_not_commute hK hq h9K hEa hxhS (mul_mem hwhS (inv_mem hyhS))
      (hxh ▸ hmkE x hxD) (hxh ▸ hψx1) ?_ ?_ hcomm
    · rw [map_mul, map_inv, hmkwh, hyh, ← map_inv, ← map_mul]
      exact hmkE _ (mul_mem hwD (inv_mem hyD))
    · rw [map_mul, map_inv, hmkwh, hyh, ← map_inv, ← map_mul, hxh]
      exact hnot_mem _ hnot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwy
  have hgy : g * y * g⁻¹ = x ^ k * y := by rw [hk]; group
  have hxk : x ^ k = 1 := by
    by_contra hxk
    have hxy : x * y = y * x := hcommD x hxD y hyD
    have hit : ∀ n : ℕ, g ^ n * y * (g ^ n)⁻¹ = x ^ (k * n) * y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hgxk : ∀ m : ℤ, g * x ^ m * g⁻¹ = x ^ m := fun m => by
          rw [← conj_zpow, show g * x * g⁻¹ = x by rw [hgx]; group]
        calc g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ = g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by group
          _ = g * (x ^ (k * n) * y) * g⁻¹ := by rw [ih]
          _ = (g * x ^ (k * n) * g⁻¹) * (g * y * g⁻¹) := by group
          _ = x ^ (k * n) * (x ^ k * y) := by rw [hgxk, hgy]
          _ = x ^ (k * (n + 1)) * y := by
            rw [← mul_assoc, ← _root_.zpow_add]
            ring_nf
    obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3
      (by norm_num)
    set h := g ^ b with hhdef
    have hh : h ^ 3 ^ a = 1 := by
      rw [hhdef, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have hhD : h ∈ Subgroup.normalizer (D : Set X) := Subgroup.pow_mem _ hgD b
    have hhmem := mem_of_isPGroup_normalizer h27 hD9 hh hhD
    have hhy : h * y * h⁻¹ = y := by
      rw [hcommD h hhmem y hyD]
      group
    rw [hhdef, hit b] at hhy
    have hxkb : x ^ (k * (b : ℤ)) = 1 := by
      have := congrArg (· * y⁻¹) hhy
      simpa using this
    apply hxk
    rw [← orderOf_dvd_iff_zpow_eq_one, hxo] at hxkb ⊢
    rcases (Int.prime_three.dvd_or_dvd hxkb) with h1 | h1
    · exact h1
    · exact absurd (Int.natCast_dvd_natCast.mp h1) hb3
  have hgy' : g * y = y * g := by
    have : g * y * g⁻¹ = y := by rw [hgy, hxk, one_mul]
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [this]
  have hDxy : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ D :=
      sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hyD)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hD9, Sec4.card_zpowers_sup_zpowers (hD.2 y hyD) hxo hyx (hcommD y hyD x hxD)]
  have hDC : D ≤ Subgroup.centralizer ({g} : Set X) := by
    rw [hDxy]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgx.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgy'.symm
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.mp (hDC hd)

end Model

theorem exists_normal_complement {X : Type} [Group X] [Finite X] (h27 : ¬ 27 ∣ Nat.card X)
    {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) {x : X}
    (hxD : x ∈ D)
    (hB : ∀ g : X, g * x = x * g → g ∈ Subgroup.normalizer (D : Set X) →
      g ∈ Subgroup.centralizer (D : Set X)) :
    ∃ N : Subgroup X, N ≤ Subgroup.centralizer ({x} : Set X) ∧ ¬ 3 ∣ Nat.card N ∧
      Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (N : Set X) ∧
      Subgroup.centralizer ({x} : Set X) ≤ N ⊔ D := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({x} : Set X) with hC
  have hDC : D ≤ C := fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨x, hxD⟩))
  set D' : Subgroup C := D.subgroupOf C with hD'
  have hD'9 : Nat.card D' = 9 := by
    rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hD9]
  have hD'3 : IsPGroup 3 D' := IsPGroup.of_card (n := 2) (by rw [hD'9]; norm_num)
  have hidx : ¬ 3 ∣ D'.index := by
    intro h3
    apply h27
    have h1 : Nat.card D' * D'.index = Nat.card C := D'.card_mul_index
    have h2 : 27 ∣ Nat.card C := by
      rw [← h1, hD'9]
      obtain ⟨t, ht⟩ := h3
      exact ⟨t, by rw [ht]; ring⟩
    exact h2.trans (Subgroup.card_subgroup_dvd_card C)
  set P : Sylow 3 C := hD'3.toSylow hidx with hP
  have hPD : (P : Subgroup C) = D' := IsPGroup.toSylow_coe hD'3 hidx
  have hnc : Subgroup.normalizer ((P : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((P : Subgroup C) : Set C) := by
    intro c hc
    rw [hPD] at hc ⊢
    have hcX : (c : X) ∈ Subgroup.normalizer (D : Set X) := by
      refine Subgroup.mem_normalizer_fintype fun d hd => ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp hc ⟨d, hDC hd⟩).mp
        (Subgroup.mem_subgroupOf.mpr hd)
      exact Subgroup.mem_subgroupOf.mp h1
    have hcx : (c : X) * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hcD := hB c hcx hcX
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcD d (Subgroup.mem_subgroupOf.mp hd)
  set N' := (MonoidHom.transferSylow P hnc).ker with hN'
  have hcompl : Subgroup.IsComplement' N' P := MonoidHom.ker_transferSylow_isComplement' P hnc
  have hN'3 : ¬ 3 ∣ Nat.card N' := MonoidHom.not_dvd_card_ker_transferSylow P hnc
  refine ⟨N'.map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective C.subtype_injective]
  · intro c hc
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨n', hn', rfl⟩ := hn
    have h1 : (⟨c, hc⟩ : C) * n' * (⟨c, hc⟩ : C)⁻¹ ∈ N' :=
      (MonoidHom.normal_ker _).conj_mem n' hn' ⟨c, hc⟩
    exact ⟨_, h1, rfl⟩
  · have hsup := hcompl.sup_eq_top
    have hmap := congrArg (Subgroup.map C.subtype) hsup
    rw [Subgroup.map_sup, hPD, hD', Subgroup.subgroupOf_map_subtype, inf_of_le_left hDC,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap.symm.le

end Proof1513Res3

open Proof1513Res3
open scoped commutatorElement

@[expose] def KS1517SeitzU : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e % 3 = 2 → Group.IsPerfect X → p ^ e % 9 ≠ 8 →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k} = ⊤

theorem ks1517CentGen_of (hU : KS1517SeitzU) : KS1517CentGen := by
  intro X _ _ p e _ he hiso hperf h9 h4 D hD hD9
  classical
  have hp : p.Prime := Fact.out
  have hiso' := hiso
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have h27 := not_dvd_card_of_equiv hK hq h9 φ
  have hgen : Subgroup.closure {k : X | ∃ x ∈ D, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    rcases hiso with ⟨hq1, ⟨ψ⟩⟩ | ⟨hq2, -⟩
    · refine closure_centralizers_eq_top_linear he hq1 ψ ?_ D hD hD9
      have hq2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      by_contra hle
      have h4eq : p ^ e = 4 := by omega
      have hp2 : p = 2 := by
        have hpd : p ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = p ^ e by omega]
          exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
      subst hp2
      have he2 : e = 2 := Nat.pow_right_injective (le_refl 2) (h4eq.trans (by norm_num))
      subst he2
      exact h4 hiso'
    · exact hU X p e he hiso' hq2 hperf (fun h => h9 (Or.inr h)) D hD hD9
  have hN : ∀ x ∈ D, x ≠ 1 → ∃ N : Subgroup X, N ≤ Subgroup.centralizer ({x} : Set X) ∧
      ¬ 3 ∣ Nat.card N ∧ Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (N : Set X) ∧
      Subgroup.centralizer ({x} : Set X) ≤ N ⊔ D := fun x hxD hx1 =>
    exists_normal_complement h27 hD hD9 hxD fun g hgx hgD =>
      mem_centralizer_of_mem_normalizer hK hq h9 φ hD hD9 hxD hx1 hgx hgD
  set 𝒯 := {T : Subgroup X | ¬ 3 ∣ Nat.card T ∧ ∃ x ∈ D, x ≠ 1 ∧
    T ≤ Subgroup.centralizer ({x} : Set X) ∧
    Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (T : Set X)} with h𝒯
  set H := sSup 𝒯 with hH
  have hDC : ∀ x ∈ D, D ≤ Subgroup.centralizer ({x} : Set X) := fun x hxD d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨x, hxD⟩))
  have hDH : D ≤ Subgroup.normalizer (H : Set X) :=
    Sec14.le_normalizer_sSup fun T ⟨_, x, hxD, _, _, hCT⟩ => (hDC x hxD).trans hCT
  have htop : H ⊔ D = ⊤ := by
    refine top_le_iff.mp (hgen ▸ (Subgroup.closure_le _).mpr ?_)
    rintro k ⟨x, hxD, hx1, hkx⟩
    obtain ⟨N, hNC, hN3, hCN, hCND⟩ := hN x hxD hx1
    have hNH : N ≤ H := le_sSup ⟨hN3, x, hxD, hx1, hNC, hCN⟩
    exact sup_le_sup_right hNH D (hCND (Subgroup.mem_centralizer_singleton_iff.mpr hkx))
  have hHn : H.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hDH
  have hmapD : ∀ g : X, QuotientGroup.mk' H g ∈ D.map (QuotientGroup.mk' H) := by
    intro g
    have hmap : (H ⊔ D).map (QuotientGroup.mk' H) = D.map (QuotientGroup.mk' H) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [← hmap, htop]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top g)
  have hcomm : ∀ g₁ g₂ : X, ⁅g₁, g₂⁆ ∈ H := by
    intro g₁ g₂
    obtain ⟨d₁, hd₁, h₁⟩ := hmapD g₁
    obtain ⟨d₂, hd₂, h₂⟩ := hmapD g₂
    have hd : d₁ * d₂ = d₂ * d₁ := congrArg Subtype.val (hD.1.is_comm.comm ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩)
    rw [← QuotientGroup.eq_one_iff (N := H), ← QuotientGroup.mk'_apply, map_commutatorElement,
      ← h₁, ← h₂, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hd,
      map_one]
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator, Subgroup.commutator_le]
  exact fun g₁ _ g₂ _ => hcomm g₁ g₂

end CFSG.RankThree.PartTwo.Sec15
