module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

@[instance_reducible]
def conjActionOfNormalizing {X : Type*} [Group X] (V O : Subgroup X)
    (hV : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O) : MulDistribMulAction V O where
  smul v o := ⟨(v : X) * (o : X) * (v : X)⁻¹, hV (v : X) v.2 (o : X) o.2⟩
  one_smul o := by
    apply Subtype.ext
    change ((1 : V) : X) * (o : X) * ((1 : V) : X)⁻¹ = (o : X)
    simp
  mul_smul v w o := by
    apply Subtype.ext
    change ((v * w : V) : X) * (o : X) * ((v * w : V) : X)⁻¹
      = (v : X) * ((w : X) * (o : X) * (w : X)⁻¹) * (v : X)⁻¹
    simp [mul_assoc]
  smul_one v := by
    apply Subtype.ext
    change (v : X) * ((1 : O) : X) * (v : X)⁻¹ = ((1 : O) : X)
    simp
  smul_mul v o o' := by
    apply Subtype.ext
    change (v : X) * ((o : X) * (o' : X)) * (v : X)⁻¹
      = ((v : X) * (o : X) * (v : X)⁻¹) * ((v : X) * (o' : X) * (v : X)⁻¹)
    simp [mul_assoc]

theorem odd_normal_eq_bot {X : Type*} [Group X] [Finite X] {H V O : Subgroup X}
    (hVH : V ≤ H) (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV4 : 4 ≤ Nat.card V)
    (hti : ∀ g : X, ∀ x ∈ V, x ≠ 1 → g * x * g⁻¹ ∈ V → g ∈ Subgroup.normalizer (V : Set X))
    (hOH : ∀ h ∈ H, h ∈ Subgroup.normalizer (O : Set X)) (hOle : O ≤ H)
    (hOodd : Odd (Nat.card O))
    (hOK : ∀ k ∈ O, k ∈ Subgroup.normalizer (V : Set X) → k = 1) : O = ⊥ := by
  have hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O := by
    intro v hv o ho
    have hvN : v ∈ Subgroup.normalizer (O : Set X) := hOH v (hVH hv)
    exact (Subgroup.mem_set_normalizer_iff.mp hvN o).mp ho
  haveI : IsMulCommutative V := IsMulCommutative.of_setLike_mul_comm hVab
  letI : CommGroup V := IsMulCommutative.instCommGroup
  letI : MulDistribMulAction V O := conjActionOfNormalizing V O hVO
  haveI : Fact (IsPGroup 2 V) :=
    ⟨fun g => ⟨1, Subtype.ext (by simpa using hV2 (g : X) g.2)⟩⟩
  have hG : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.mpr hOodd
  have hncyc : ¬ IsCyclic V := by
    intro hcyc
    have he : Monoid.exponent V = Nat.card V := IsCyclic.exponent_eq_card
    have hdvd : Monoid.exponent V ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hV2 (g : X) g.2)
    rw [he] at hdvd
    have hle2 : Nat.card V ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥O) (A := ↥V) 2 hG hncyc
  have hle : (⨆ (a : V) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) O) ≤ ⊥ := by
    refine iSup₂_le ?_
    intro a ha g hg
    rw [FixedPoints.mem_subgroup] at hg
    have h1 := hg ⟨a, Subgroup.mem_zpowers a⟩
    have h2 : (a : X) * (g : X) * (a : X)⁻¹ = (g : X) := congrArg Subtype.val h1
    have h3 : (a : X) * (g : X) = (g : X) * (a : X) := mul_inv_eq_iff_eq_mul.mp h2
    have hcalc : (g : X) * (a : X) * (g : X)⁻¹ = (a : X) := by
      rw [← h3]
      simp
    have hconj : (g : X) * (a : X) * (g : X)⁻¹ ∈ V := by
      rw [hcalc]
      exact a.2
    have ha1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
    have hnorm : (g : X) ∈ Subgroup.normalizer (V : Set X) :=
      hti (g : X) (a : X) a.2 ha1 hconj
    have hg1 : (g : X) = 1 := hOK (g : X) g.2 hnorm
    exact Subgroup.mem_bot.mpr (Subtype.ext hg1)
  have htop : (⊤ : Subgroup O) ≤ ⊥ := by
    rw [← hgen]
    exact hle
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hmem : (⟨x, hx⟩ : O) ∈ (⊥ : Subgroup O) := htop (Subgroup.mem_top _)
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

end CFSG.RankThree.GF2n.Stroth80
