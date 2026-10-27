module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma710
public import CFSG.Quasithin.Recognition.F112Crit.ConjAut

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

theorem relIndex_stab_inf_le_card_nbrs {α₁ α₂ : CosetGeom G₀ G₁ G₂} {W : Subgroup G}
    (hW : W ≤ stab α₂) (hα₁ : α₁ ∈ nbrs α₂) :
    (W ⊓ stab α₁).relIndex W ≤ Nat.card (nbrs α₂) := by
  have hWG₀ : W ≤ G₀ := hW.trans (CosetGeom.stab_le α₂)
  letI : MulAction ↥W (CosetGeom G₀ G₁ G₂) := MulAction.compHom _ (Subgroup.inclusion hWG₀)
  have hsm : ∀ g : ↥W, g • α₁ = (⟨(g : G), hWG₀ g.2⟩ : ↥G₀) • α₁ := fun g => rfl
  have horb : MulAction.orbit ↥W α₁ ⊆ nbrs α₂ := by
    rintro ε ⟨g, rfl⟩
    show g • α₁ ∈ nbrs α₂
    rw [hsm]
    exact IsLocalReg.smul_mem_nbrs (g := ⟨(g : G), hWG₀ g.2⟩) hα₁ (hW g.2)
  have hstab : MulAction.stabilizer ↥W α₁ = (W ⊓ stab α₁).subgroupOf W := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsm]
    constructor
    · intro hg
      exact ⟨g.2, CosetGeom.mem_stab_of_smul_eq hg⟩
    · intro hg
      exact CosetGeom.smul_eq_of_mem_stab hg.2
  calc (W ⊓ stab α₁).relIndex W = (MulAction.stabilizer ↥W α₁).index := by
        rw [hstab]; rfl
    _ = (MulAction.orbit ↥W α₁).ncard := MulAction.index_stabilizer ↥W α₁
    _ ≤ (nbrs α₂).ncard := Set.ncard_le_ncard horb
    _ = Nat.card (nbrs α₂) := (Nat.card_coe_set_eq _).symm

theorem relIndex_stab_inf_le_card_nbrs_sub_one {α₁ α₂ : CosetGeom G₀ G₁ G₂} {W : Subgroup G}
    (hW : W ≤ stab α₂) (hα₁ : α₁ ∈ nbrs α₂) (hWp : IsPGroup 2 ↥W)
    (hodd : Odd (Nat.card (nbrs α₂))) (hne : 1 < Nat.card (nbrs α₂)) :
    (W ⊓ stab α₁).relIndex W ≤ Nat.card (nbrs α₂) - 1 := by
  have hle := relIndex_stab_inf_le_card_nbrs hW hα₁
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  have hdvd : (W ⊓ stab α₁).relIndex W ∣ 2 ^ n := by
    rw [← hn]; exact Subgroup.relIndex_dvd_card _ _
  have hne' : (W ⊓ stab α₁).relIndex W ≠ Nat.card (nbrs α₂) := by
    intro heq
    rw [heq] at hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero] at hm
      omega
    · have h2 : 2 ∣ Nat.card (nbrs α₂) := by
        rw [hm]; exact dvd_pow_self 2 hpos.ne'
      obtain ⟨k, hk⟩ := hodd
      omega
  omega

theorem relIndex_stab_inf_stab_le_two (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₁ : Subgroup G}
    {α₁ α₂ : CosetGeom G₀ G₁ G₂} (h₁ : IsLocalReg α₁ p X₁) (hα₁ : α₁ ∈ nbrs (γ₀ G₀ G₁ G₂))
    (hα₂ : α₂ ∈ nbrs α₁) {W : Subgroup G} (hel2 : ∀ v ∈ W, v * v = 1) (hW : W ≤ stab α₂) :
    (W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂)).relIndex (W ⊓ stab α₁) ≤ 2 := by
  have hγα₁ : γ₀ G₀ G₁ G₂ ∈ nbrs α₁ := CosetGeom.mem_nbrs_symm hα₁
  have hker : ballStab 1 α₁ ≤ stab (γ₀ G₀ G₁ G₂) := IsLocalReg.ker_le_stab_of_mem_nbrs hγα₁
  refine relIndex_le_two_of_forall fun a ha b hb haA hbA => ?_
  have hsq : ∀ c ∈ W ⊓ stab α₁, c * c ∈ ballStab 1 α₁ := fun c hc' => by
    rw [hel2 c hc'.1]; exact Subgroup.one_mem _
  have hane : a ∉ ballStab 1 α₁ := fun h => haA ⟨ha, hker h⟩
  have hbne : b ∉ ballStab 1 α₁ := fun h => hbA ⟨hb, hker h⟩
  have hmem : b * a ∈ ballStab 1 α₁ :=
    h₁.mul_mem_ker hc.amalgam.gen hα₂ ⟨hb.2, hW hb.1⟩ ⟨ha.2, hW ha.1⟩ (hsq b hb) (hsq a ha)
      hbne hane
  exact ⟨(W ⊓ stab α₁).mul_mem hb ha, hker hmem⟩

theorem card_commSubgroup_le_two_mul_relIndex (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ}
    {X₁ : Subgroup G} {α₁ α₂ : CosetGeom G₀ G₁ G₂} (h₁ : IsLocalReg α₁ p X₁)
    (hα₁ : α₁ ∈ nbrs (γ₀ G₀ G₁ G₂)) (hα₂ : α₂ ∈ nbrs α₁) {W : Subgroup G} [IsMulCommutative ↥W]
    (hel2 : ∀ v ∈ W, v * v = 1) (hW : W ≤ stab α₂) {z : G} (hz : z ∈ Z)
    (hzW : z ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card (ConjAut.commSubgroup W z) ≤ 2 * (W ⊓ stab α₁).relIndex W := by
  have hstep1 : Nat.card (ConjAut.commSubgroup W z) =
      (Subgroup.centralizer ({z} : Set G)).relIndex W := by
    rw [ConjAut.card_commSubgroup W z hzW, GaloisDescent.card_commSub_eq_index,
      ConjAut.index_fixSub_conjAut]
  have hA₀C : W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro g hg
    have hg1 : g ∈ G₁ := by
      have h := hg.2
      rwa [hc.stab_γ₀_eq] at h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact (Subgroup.mem_centralizer_iff.mp (hc.centralizes hg1)) z hz
  have hA₀ne : (W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂)).relIndex W ≠ 0 := fun h0 => by
    have hd := Subgroup.relIndex_dvd_card (W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂)) W
    rw [h0, zero_dvd_iff] at hd
    exact Nat.card_pos.ne' hd
  have hA₀A₁ : W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂) ≤ W ⊓ stab α₁ := inf_le_left
  have hA₁W : W ⊓ stab α₁ ≤ W := inf_le_left
  have h2 := relIndex_stab_inf_stab_le_two hc h₁ hα₁ hα₂ hel2 hW
  calc Nat.card (ConjAut.commSubgroup W z) = (Subgroup.centralizer ({z} : Set G)).relIndex W :=
        hstep1
    _ ≤ (W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂)).relIndex W :=
        Subgroup.relIndex_le_of_le_left hA₀C hA₀ne
    _ = (W ⊓ stab α₁ ⊓ stab (γ₀ G₀ G₁ G₂)).relIndex (W ⊓ stab α₁) *
          (W ⊓ stab α₁).relIndex W :=
        (Subgroup.relIndex_mul_relIndex _ _ _ hA₀A₁ hA₁W).symm
    _ ≤ 2 * (W ⊓ stab α₁).relIndex W := Nat.mul_le_mul h2 le_rfl

theorem card_commSubgroup_le_aux (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₁ : Subgroup G}
    {α₁ α₂ : CosetGeom G₀ G₁ G₂} (h₁ : IsLocalReg α₁ p X₁) (hα₁ : α₁ ∈ nbrs (γ₀ G₀ G₁ G₂))
    (hα₂ : α₂ ∈ nbrs α₁) {W : Subgroup G} [IsMulCommutative ↥W] (hel2 : ∀ v ∈ W, v * v = 1)
    (hWp : IsPGroup 2 ↥W) (hW : W ≤ stab α₂) (hodd : Odd (Nat.card (nbrs α₂)))
    (hne : 1 < Nat.card (nbrs α₂)) {z : G} (hz : z ∈ Z)
    (hzW : z ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card (ConjAut.commSubgroup W z) ≤ 2 * (Nat.card (nbrs α₂) - 1) :=
  (card_commSubgroup_le_two_mul_relIndex hc h₁ hα₁ hα₂ hel2 hW hz hzW).trans
    (Nat.mul_le_mul le_rfl
      (relIndex_stab_inf_le_card_nbrs_sub_one hW (CosetGeom.mem_nbrs_symm hα₂) hWp hodd hne))

theorem card_commSubgroup_Wv_le (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hb : 4 ≤ critB G₀ G₁ G₂ Z)
    {α₁ α₂ α' : CosetGeom G₀ G₁ G₂} (hα₁ : α₁ ∈ nbrs (γ₀ G₀ G₁ G₂)) (hα₂ : α₂ ∈ nbrs α₁)
    (hα' : vtype α' = false) (hW : Wv Z α' ≤ stab α₂)
    (hodd : Odd (Nat.card (nbrs α₂))) (hne : 1 < Nat.card (nbrs α₂))
    {z : G} (hz : z ∈ Z) (hzα' : z ∈ stab α') :
    Nat.card (ConjAut.commSubgroup (Wv Z α') z) ≤ 2 * (Nat.card (nbrs α₂) - 1) := by
  have hel : IsElemAbelian 2 (Wv Z α') := isElemAbelian_Wv hc hb hα'
  haveI : IsMulCommutative ↥(Wv Z α') := hel.1
  obtain ⟨X₁, h₁⟩ :=
    exists_isLocalReg_of_vtype hloc (vtype_eq_true_of_mem_nbrs CosetGeom.vtype_γ₀ hα₁)
  exact card_commSubgroup_le_aux hc h₁ hα₁ hα₂ (fun v hv => by rw [← pow_two]; exact hel.2 v hv)
    (isPGroup_of_isElemAbelian hel) hW hodd hne hz (stab_le_normalizer_Wv hc α' hzα')

end CFSG.Quasithin.F112Crit

end
