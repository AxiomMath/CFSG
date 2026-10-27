module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bF
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec12.Item125Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem s7_holds : S7 := by
  intro G _ _ A c L E F a b R Y hY
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hY.hCfg
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨-, -, -, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  rw [← hsup]
  exact sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)

theorem exists_mul_of_mem_sup {G : Type} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * (k₁ * h₂ * k₁⁻¹), mul_mem hh₁ ?_, k₁ * k₂, mul_mem hk₁ hk₂, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hK hk₁) h₂).mp hh₂
      one_mem' := ⟨1, one_mem H, 1, one_mem K, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, inv_mem hk, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hK (inv_mem hk)) h⁻¹).mp (inv_mem hh)
        simpa using this }
  have hle : H ⊔ K ≤ S :=
    sup_le (fun h hh => ⟨h, hh, 1, one_mem K, by simp⟩) (fun k hk => ⟨1, one_mem H, k, hk, by simp⟩)
  exact hle hx

theorem mul_pow_three_of_commutator_central' {G : Type} [Group G] {x y c : G}
    (hyx : y * x = c * (x * y)) (hxc : x * c = c * x) (hyc : y * c = c * y) (hc3 : c ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hc3' : c * (c * c) = 1 := by simpa [pow_succ, mul_assoc] using hc3
  have h2 : y * y * x = c * c * (x * (y * y)) := by
    calc y * y * x = y * (y * x) := by group
      _ = y * (c * (x * y)) := by rw [hyx]
      _ = (y * c) * (x * y) := by group
      _ = (c * y) * (x * y) := by rw [hyc]
      _ = c * (y * x) * y := by group
      _ = c * (c * (x * y)) * y := by rw [hyx]
      _ = c * c * (x * (y * y)) := by group
  have hx2c : x * x * (c * c) = c * c * (x * x) := by
    calc x * x * (c * c) = x * (x * c) * c := by group
      _ = x * (c * x) * c := by rw [hxc]
      _ = (x * c) * (x * c) := by group
      _ = (c * x) * (c * x) := by rw [hxc]
      _ = c * (x * c) * x := by group
      _ = c * (c * x) * x := by rw [hxc]
      _ = c * c * (x * x) := by group
  have e1 : (x * y) ^ 3 = x * y * x * y * x * y := by simp [pow_succ, mul_assoc]
  have e2 : x ^ 3 * y ^ 3 = x * x * x * (y * y * y) := by simp [pow_succ, mul_assoc]
  rw [e1, e2]
  calc x * y * x * y * x * y = x * (y * x) * y * x * y := by group
    _ = x * (c * (x * y)) * y * x * y := by rw [hyx]
    _ = (x * c) * (x * y) * y * x * y := by group
    _ = (c * x) * (x * y) * y * x * y := by rw [hxc]
    _ = c * x * x * (y * y * x) * y := by group
    _ = c * x * x * (c * c * (x * (y * y))) * y := by rw [h2]
    _ = c * (x * x * (c * c)) * (x * (y * y)) * y := by group
    _ = c * (c * c * (x * x)) * (x * (y * y)) * y := by rw [hx2c]
    _ = (c * (c * c)) * (x * x * x * (y * y * y)) := by group
    _ = x * x * x * (y * y * y) := by rw [hc3', one_mul]

theorem pow_three_mul_eq_one {G : Type} [Group G] {e y : G} {Z : Subgroup G}
    (he : e ^ 3 = 1) (hy : y ^ 3 = 1) (hZ : ∀ z ∈ Z, z ^ 3 = 1)
    (hzE : ∀ z ∈ Z, e * z = z * e) (hzY : ∀ z ∈ Z, y * z = z * y)
    (hcomm : y * e * y⁻¹ * e⁻¹ ∈ Z) : (e * y) ^ 3 = 1 := by
  have h := mul_pow_three_of_commutator_central' (x := e) (y := y) (c := y * e * y⁻¹ * e⁻¹)
    (by group) (hzE _ hcomm) (hzY _ hcomm) (hZ _ hcomm)
  rw [h, he, hy, one_mul]

theorem s5_holds : S5 := by
  intro G _ _ A c L E F a b R Y hY
  have hEe := hY.hCfg.hEe
  have hE27 := hY.hCfg.hE27
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hY.hD.isElemAbelian
  have hF27 : Nat.card F = 27 := hY.hD.card_eq
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcard : Nat.card (E ⊔ F : Subgroup G) = 81 := by
    have h := Sec6.card_sup_mul_card_inf hY.hFE
    rw [sup_comm, inf_comm, hY.hFEcard, hF27, hE27] at h
    omega
  have hp : IsPGroup 3 (E ⊔ F : Subgroup G) := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hcE := hY.hcE
  have hcF := hY.hcF
  have hZ3 : ∀ z ∈ Subgroup.zpowers c, z ^ 3 = 1 :=
    (Item131bProof.isElemAbelian_zpowers (hEe.2 c hcE)).2
  have hexp : ∀ x ∈ (E ⊔ F : Subgroup G), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, f, hf, rfl⟩ := exists_mul_of_mem_sup hY.hFE hx
    have hz := hY.hcomm f hf e he
    refine pow_three_mul_eq_one (hEe.2 e he) (hFe.2 f hf) hZ3 ?_ ?_ hz
    · intro z hz'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ((show Commute e c from hEcomm e he c hcE).zpow_right j).eq
    · intro z hz'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ((show Commute f c from hFcomm f hf c hcF).zpow_right j).eq
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx b hY.hbE)
  have hFb : F ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm x hx b hY.hD.mem_A)
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    hY.hCfg.hEle.trans (inf_le_left.trans (sup_le Subgroup.le_normalizer hY.hCfg.hD.le_normalizer))
  have hFL : F ≤ Subgroup.normalizer (L : Set G) := by
    calc F = Subgroup.zpowers a ⊔ (E ⊓ F) := hY.hFgen
      _ ≤ Subgroup.normalizer (L : Set G) :=
        sup_le (Subgroup.zpowers_le.mpr (hY.hCfg.hD.le_normalizer hY.haA)) (inf_le_left.trans hEL)
  exact ⟨hcard, hp, hexp, le_inf (le_inf (sup_le Subgroup.le_normalizer hY.hFE) (sup_le hEb hFb))
    (sup_le hEL hFL)⟩

theorem s6_holds : S6 := by
  intro G _ _ A c L E F a b R Y hY ρ hρ
  have hEe := hY.hCfg.hEe
  have hE27 := hY.hCfg.hE27
  have hcE := hY.hcE
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := hEe.2 c hcE
  have hc1 : c ≠ 1 := hY.hCfg.hD.ne_one
  have hρ1 : ρ ≠ 1 := fun h => hρ.not_mem (h ▸ one_mem E)
  have hρc : ρ * c = c * ρ := by
    have hm : ρ * c * ρ⁻¹ ∈ Subgroup.zpowers c := by
      have h := hρ.comm_E c hcE
      have h2 := mul_mem h (Subgroup.mem_zpowers c)
      simpa using h2
    rcases eq_of_mem_zpowers_of_pow_three hc3 hm with h1 | h1 | h1
    · exfalso
      apply hc1
      have : c = ρ⁻¹ * (ρ * c * ρ⁻¹) * ρ := by group
      rw [this, h1]
      group
    · exact mul_inv_eq_iff_eq_mul.mp h1
    · exfalso
      have h2 : ρ * c ^ 2 * ρ⁻¹ = c := by
        calc ρ * c ^ 2 * ρ⁻¹ = (ρ * c * ρ⁻¹) ^ 2 := conj_pow.symm
          _ = (c ^ 2) ^ 2 := by rw [h1]
          _ = c ^ 3 * c := by group
          _ = c := by rw [hc3, one_mul]
      have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three']; exact hρ.pow_three
      have h4 : c = c ^ 2 := by
        calc c = (ρ * ρ * ρ) * c * (ρ * ρ * ρ)⁻¹ := by rw [hρ3']; simp
          _ = ρ * (ρ * (ρ * c * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by simp [mul_assoc]
          _ = ρ * (ρ * c ^ 2 * ρ⁻¹) * ρ⁻¹ := by rw [h1]
          _ = ρ * c * ρ⁻¹ := by rw [h2]
          _ = c ^ 2 := h1
      apply hc1
      have h5 : c = c * c := by rw [← pow_two]; exact h4
      simpa using h5
  have hZE : ∀ z ∈ Subgroup.zpowers c, ∀ e ∈ E, e * z = z * e := by
    intro z hz' e he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    exact ((show Commute e c from hEcomm e he c hcE).zpow_right j).eq
  obtain ⟨K, hK⟩ := exists_subgroup_comm_zpowers hZE
  have hρK : ρ ∈ K := by
    refine (hK ρ).mpr ⟨?_, hρ.comm_E⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (show h ∈ Subgroup.zpowers c from hh)
    exact (((show Commute ρ c from hρc).zpow_right j).eq).symm
  have hZ3 : ∀ z ∈ Subgroup.zpowers c, z ^ 3 = 1 := (Item131bProof.isElemAbelian_zpowers hc3).2
  have hord : orderOf ρ = 3 := orderOf_eq_prime hρ.pow_three hρ1
  have hbot : E ⊓ Subgroup.zpowers ρ = ⊥ := Sec12.inf_zpowers_eq_bot_of_not_mem hord hρ.not_mem
  have hcard : Nat.card (E ⊔ Subgroup.zpowers ρ : Subgroup G) = 81 := by
    have h := Sec6.card_sup_mul_card_inf (Subgroup.zpowers_le.mpr hρ.mem_normalizer_E)
    rw [sup_comm, inf_comm, hbot, Subgroup.card_bot, Nat.card_zpowers, hord, hE27] at h
    omega
  have hp : IsPGroup 3 (E ⊔ Subgroup.zpowers ρ : Subgroup G) :=
    IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hρ3z : ∀ y ∈ Subgroup.zpowers ρ, y ^ 3 = 1 :=
    (Item131bProof.isElemAbelian_zpowers hρ.pow_three).2
  have hexp : ∀ x ∈ (E ⊔ Subgroup.zpowers ρ : Subgroup G), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, y, hy, rfl⟩ := exists_mul_of_mem_sup
      (Subgroup.zpowers_le.mpr hρ.mem_normalizer_E) hx
    have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hρK) hy
    obtain ⟨hyC, hyE⟩ := (hK y).mp hyK
    refine pow_three_mul_eq_one (hEe.2 e he) (hρ3z y hy) hZ3 (hZE · · e he) ?_ (hyE e he)
    intro z hz'
    exact (Subgroup.mem_centralizer_iff.mp hyC z hz').symm
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx b hY.hbE)
  have hEL : E ≤ Subgroup.normalizer (L : Set G) :=
    hY.hCfg.hEle.trans (inf_le_left.trans (sup_le Subgroup.le_normalizer hY.hCfg.hD.le_normalizer))
  have hρb : ρ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hρ.comm_b
  refine ⟨hcard, hp, hexp, le_inf (le_inf (sup_le Subgroup.le_normalizer
    (Subgroup.zpowers_le.mpr hρ.mem_normalizer_E)) (sup_le hEb (Subgroup.zpowers_le.mpr hρb)))
    (sup_le hEL (Subgroup.zpowers_le.mpr hρ.mem_normalizer_L))⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
