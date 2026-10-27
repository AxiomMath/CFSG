module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompW
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompH
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompU
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompV

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

theorem map_conj_mul {G : Type*} [Group G] (L : Subgroup G) (c c' : G) :
    L.map (MulAut.conj (c * c')).toMonoidHom =
      (L.map (MulAut.conj c').toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem normalizer_of_component (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x)) : Gw d x ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hne
  rw [IsConcreteLE.not_le_iff_exists] at hne
  obtain ⟨g₀, hg₀G, hg₀N⟩ := hne
  set L₂ : Subgroup G := L.map (MulAut.conj g₀).toMonoidHom with hL₂def
  have hL₂ : IsComponentIn L₂ (Gw d x) := isComponentIn_conj hL hg₀G
  have hne12 : L ≠ L₂ := fun e => hg₀N (map_conj_eq_iff.mp e.symm)
  have hall : ∀ Λ : Subgroup G, IsComponentIn Λ (Gw d x) → Λ = L ∨ Λ = L₂ := by
    intro Λ hΛ
    by_contra hcon
    rw [not_or] at hcon
    exact three_components_Gw h hf hL hL₂ hΛ hne12 (Ne.symm hcon.1) (Ne.symm hcon.2)
  have hinj : ∀ {c : G} {A B : Subgroup G},
      A.map (MulAut.conj c).toMonoidHom = B.map (MulAut.conj c).toMonoidHom → A = B :=
    fun e => Subgroup.map_injective (MulAut.conj _).injective e
  set N : Subgroup ↥(Gw d x) := (Subgroup.normalizer (L : Set G)).subgroupOf (Gw d x) with hNdef
  have hmemN : ∀ b : ↥(Gw d x), b ∈ N ↔ L.map (MulAut.conj (b : G)).toMonoidHom = L := fun b =>
    Subgroup.mem_subgroupOf.trans map_conj_eq_iff.symm
  have hidx : N.index = 2 := by
    refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨g₀, hg₀G⟩, ?_, fun b => ?_⟩
    · exact fun hmem => hg₀N (Subgroup.mem_subgroupOf.mp hmem)
    · rcases hall _ (isComponentIn_conj hL b.2) with hb | hb
      · exact Or.inr ((hmemN b).mpr hb)
      · left
        rw [hmemN]
        have hb2 : L.map (MulAut.conj ((b * ⟨g₀, hg₀G⟩ : ↥(Gw d x)) : G)).toMonoidHom =
            L₂.map (MulAut.conj (b : G)).toMonoidHom := by
          rw [hL₂def, Subgroup.coe_mul, map_conj_mul]
        rw [hb2]
        rcases hall _ (isComponentIn_conj hL₂ b.2) with hb' | hb'
        · exact hb'
        · exfalso
          apply hne12
          apply hinj (c := (b : G))
          rw [hb, hb']
  have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (↥(Gw d x) ⧸ N) = 2 := hidx
  have : Fact (Nat.Prime (Nat.card (↥(Gw d x) ⧸ N))) := ⟨by rw [hcard]; exact Nat.prime_two⟩
  have hcyc : IsCyclic (↥(Gw d x) ⧸ N) := isCyclic_of_prime_card rfl
  have hcomm : IsMulCommutative (↥(Gw d x) ⧸ N) := inferInstance
  have hodd : ∀ k : ↥(Gw d x), Odd (orderOf k) → k ∈ N := by
    intro k hk
    have h1 : orderOf (QuotientGroup.mk' N k) ∣ orderOf k := orderOf_map_dvd _ k
    have h2 : orderOf (QuotientGroup.mk' N k) ∣ 2 := by
      rw [← hcard]; exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk' N k) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
      · exact h4
      · exact absurd (h4 ▸ h1) (by
          intro h5; exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h5))
    exact (QuotientGroup.eq_one_iff k).mp (orderOf_eq_one_iff.mp h3)
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_subgroupOf.mp (hodd ⟨x, h.x_mem_Gw⟩ (by rw [Subgroup.orderOf_mk, h.hx3]; decide))
  have hzN : (d * d) ∈ Subgroup.normalizer (L : Set G) :=
    ((lemma115Hyp_Gw h).component_action hL).1
  set π := QuotientGroup.mk' N with hπ
  set dX : ↥(Gw d x) := ⟨d, h.d_mem_Gw⟩ with hdX
  set xX : ↥(Gw d x) := ⟨x, h.x_mem_Gw⟩ with hxX
  have hπx : π xX = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxN)
  have hπz : π (dX * dX) = 1 :=
    (QuotientGroup.eq_one_iff (dX * dX)).mpr (Subgroup.mem_subgroupOf.mpr hzN)
  have hπd1 : π (xX * dX * xX⁻¹) = π dX := by simp [map_mul, map_inv, hπx]
  have hπd2 : π (xX * (xX * dX * xX⁻¹) * xX⁻¹) = π dX := by simp [map_mul, map_inv, hπx]
  have hu0N : u0Of d x ∈ Subgroup.normalizer (L : Set G) := by
    have hu : (⟨u0Of d x, h.u0_mem_Gw⟩ : ↥(Gw d x)) =
        (xX * dX * xX⁻¹) * (xX * (xX * dX * xX⁻¹) * xX⁻¹) := rfl
    have h1 : π ⟨u0Of d x, h.u0_mem_Gw⟩ = 1 := by
      rw [hu, map_mul, hπd1, hπd2, ← map_mul, hπz]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hK0N : K0 T d x ≤ Subgroup.normalizer (L : Set G) := by
    refine K0_le_of_odd_and_u0 h (fun k hk hodd' => ?_) hu0N
    exact Subgroup.mem_subgroupOf.mp
      (hodd ⟨k, hk.2⟩ (by rw [Subgroup.orderOf_mk]; exact hodd'))
  have hK0N₂ : K0 T d x ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro k hk
    have hkN : (⟨k, hk.2⟩ : ↥(Gw d x)) ∈ N := Subgroup.mem_subgroupOf.mpr (hK0N hk)
    have hc : g₀⁻¹ * k * g₀ ∈ Subgroup.normalizer (L : Set G) := by
      have := hnorm.conj_mem _ hkN (⟨g₀, hg₀G⟩⁻¹)
      have h' := Subgroup.mem_subgroupOf.mp this
      simpa using h'
    rw [← map_conj_eq_iff]
    calc L₂.map (MulAut.conj k).toMonoidHom = L.map (MulAut.conj (k * g₀)).toMonoidHom :=
          (map_conj_mul L k g₀).symm
      _ = L.map (MulAut.conj (g₀ * (g₀⁻¹ * k * g₀))).toMonoidHom := by
          rw [show k * g₀ = g₀ * (g₀⁻¹ * k * g₀) by group]
      _ = (L.map (MulAut.conj (g₀⁻¹ * k * g₀)).toMonoidHom).map (MulAut.conj g₀).toMonoidHom :=
          map_conj_mul L g₀ _
      _ = L₂ := by rw [map_conj_eq_iff.mpr hc]
  set Z : Subgroup G := Gw d x ⊓ Subgroup.centralizer (L : Set G) with hZdef
  have hZc : ∀ c ∈ Gw d x,
      (∀ u ∈ K0 T d x, ∀ k ∈ Z.map (MulAut.conj c).toMonoidHom,
        u * k * u⁻¹ ∈ Z.map (MulAut.conj c).toMonoidHom) ∧
      d * d ∉ Z.map (MulAut.conj c).toMonoidHom := by
    intro c hc
    rw [hZdef, map_conj_inf_centralizer hc]
    have hΛ := isComponentIn_conj hL hc
    have hKΛ : K0 T d x ≤
        Subgroup.normalizer ((L.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
      rcases hall _ hΛ with e | e
      · rw [e]; exact hK0N
      · rw [e]; exact hK0N₂
    exact ⟨fun u hu k hk => conj_mem_inf_centralizer' (H' := K0 T d x) (H := Gw d x)
      (fun y (hy : y ∈ K0 T d x) => (hy.2 : y ∈ Gw d x)) hKΛ hu hk,
      fun hz => not_mem_centralizer_z h hΛ hz.2⟩
  have hwZ : wOfX d x ∈ Z := ⟨h.w_mem_Gw, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    mem_Gw_iff.mp (hL.1 hl)⟩
  have hL₂Z : L₂ ≤ Z := fun y hy => ⟨hL₂.1 hy, Subgroup.mem_centralizer_iff.mpr fun l hl =>
    commute_of_isComponentIn_ne hL hL₂ hne12 hl hy⟩
  exact not_component_le_conj h hf.wp0 inf_le_left hZc hwZ hL₂ hL₂Z

end Main

end InspW2

end S143

end CFSG.Quasithin
