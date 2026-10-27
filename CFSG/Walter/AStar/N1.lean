module

public import CFSG.GroupTheory.PCore.Defs
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.Walter.Defs

public section

namespace CFSG.Walter

open scoped IsMulCommutative commutatorElement

theorem oddCore_eq_bot_of_centralizer_eq_bot {W : Type*} [Group W] [Finite W] (L : Subgroup W)
    [L.Normal] [IsSimpleGroup L] (hLnonab : ∃ a b : L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set W) = ⊥) : CFSG.oddCore W = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro M ⟨hMn, hModd⟩
  have := hMn.subgroupOf L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf L) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    have hcomm : ⁅M, L⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_le_inf M L).trans (disjoint_iff_inf_le.mp h))
    rw [← le_bot_iff, ← hC]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    have hLodd : Odd (Nat.card L) := Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_le h)
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hLodd
    obtain ⟨a, b, hab⟩ := hLnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem sylow_le_of_centralizer_eq_bot {W : Type} [Group W] [Finite W] (S : Sylow 2 W)
    (hS : IsMulCommutative (S : Subgroup W)) (L : Subgroup W) [L.Normal] [IsSimpleGroup L]
    (hLnonab : ∃ a b : L, a * b ≠ b * a) (hC : Subgroup.centralizer (L : Set W) = ⊥)
    (hgen : L ⊔ (S : Subgroup W) = ⊤) : (S : Subgroup W) ≤ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg := (S : Subgroup W) with hSg
  have hcommS : ∀ a b : Sg, a * b = b * a := fun a b => hS.is_comm.comm a b
  have hWL : commutator W ≤ L := by
    have hmap : Sg.map (QuotientGroup.mk' L) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' L)) hgen
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L),
        (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq] at h
      exact h
    have : IsMulCommutative (W ⧸ L) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Sg.map (QuotientGroup.mk' L) := hmap ▸ Subgroup.mem_top a
      have hb : b ∈ Sg.map (QuotientGroup.mk' L) := hmap ▸ Subgroup.mem_top b
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hcommS ⟨x, hx⟩ ⟨y, hy⟩)
    have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' L)
    rwa [QuotientGroup.ker_mk'] at h
  set N := Subgroup.normalizer (Sg : Set W) with hN
  set φ : N →* MulAut Sg := Sg.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut Sg) := φ.range with hA
  let : MulDistribMulAction A Sg := MulDistribMulAction.compHom Sg A.subtype
  have hφapp : ∀ (n : N) (x : Sg), ((φ n x : Sg) : W) = (n : W) * (x : W) * (n : W)⁻¹ :=
    fun _ _ => rfl
  have hAodd : ¬ 2 ∣ Nat.card A := by
    have hSN : Sg ≤ N := Subgroup.le_normalizer
    have hker : Sg.subgroupOf N ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcommS ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card A := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Sg.subgroupOf N).index := Subgroup.index_dvd_of_le hker
    have h3 : (Sg.subgroupOf N).index ∣ Sg.index := Subgroup.relIndex_dvd_index_of_le hSN
    intro h
    rw [← h1] at h
    exact S.not_dvd_index (h.trans (h2.trans h3))
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Sg) := by
    rw [S.card_eq_multiplicity]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hAodd).symm
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := Sg) (A := A) (Group.isSolvable_of_comm hcommS) hcop hS
  have hcommL : CFSG.commutatorAction A Sg ≤ L.subgroupOf Sg := by
    rw [CFSG.commutatorAction, CFSG.commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨a, h, -, rfl⟩
    obtain ⟨n, hn⟩ := a.2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    change ((h⁻¹ : Sg) : W) * (((a : MulAut Sg) h : Sg) : W) ∈ L
    rw [← hn, hφapp]
    apply hWL
    have : (h : W)⁻¹ * ((n : W) * (h : W) * (n : W)⁻¹) = ⁅(h : W)⁻¹, (n : W)⁆ := by
      rw [commutatorElement_def, inv_inv, ← mul_assoc, ← mul_assoc]
    rw [InvMemClass.coe_inv, this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  by_contra hSL
  have hfix : CFSG.fixedPointSubgroup A Sg ≠ ⊥ := by
    intro hbot
    apply hSL
    have htop : CFSG.commutatorAction A Sg = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    intro x hx
    have := hcommL (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : Sg))
    exact Subgroup.mem_subgroupOf.mp this
  set F := CFSG.fixedPointSubgroup A Sg with hF
  have h2F : 2 ∣ Nat.card F := by
    rcases (S.isPGroup'.to_subgroup F).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hfix
    · exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 h2F
  set z : Sg := (u : Sg) with hz_def
  have hzord : orderOf z = 2 := by rw [hz_def, Subgroup.orderOf_coe, hu]
  have hzfix : ∀ n : N, (n : W) * (z : W) * (n : W)⁻¹ = z := by
    intro n
    rw [← hφapp]
    exact congrArg Subtype.val (u.2 ⟨φ n, n, rfl⟩)
  have hzZ : z ∈ Subgroup.center Sg := Subgroup.mem_center_iff.mpr fun y => hcommS y z
  have hwc : ∀ g : W, g⁻¹ * (z : W) * g ∈ Sg → g⁻¹ * (z : W) * g = z := by
    intro g hg
    have := hS
    obtain ⟨n, hn, heq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S (z : W) g z.2 hg
    rw [heq]
    have := hzfix ⟨n⁻¹, inv_mem hn⟩
    rwa [inv_inv] at this
  obtain ⟨hfact, -⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S z hzZ hzord hwc
  have hodd := oddCore_eq_bot_of_centralizer_eq_bot L hLnonab hC
  have hzC : (z : W) ∈ Subgroup.centralizer (L : Set W) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    obtain ⟨c, hc, k, hk, hlck⟩ := hfact l
    rw [hodd, Subgroup.mem_bot] at hk
    rw [hk, mul_one] at hlck
    rw [Subgroup.mem_centralizer_iff] at hc
    rw [hlck]
    exact (hc (z : W) rfl).symm
  rw [hC, Subgroup.mem_bot] at hzC
  have : orderOf z = 1 := by
    rw [orderOf_eq_one_iff]
    exact Subtype.ext hzC
  omega

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem exists_inner_of_sylow_le_normalizer {Y : Type} [Group Y] [Finite Y]
    (hY : HasAbelianSylowTwo Y) (K : Subgroup Y) [IsSimpleGroup K]
    (hKnonab : ∃ a b : K, a * b ≠ b * a) (S : Sylow 2 Y)
    (hSK : (S : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y)) :
    ∀ s ∈ (S : Subgroup Y), ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Y := K ⊔ (S : Subgroup Y) with hH
  have hKH : K ≤ H := le_sup_left
  have hSH : (S : Subgroup Y) ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (K : Set Y) := sup_le Subgroup.le_normalizer hSK
  set K' : Subgroup H := K.subgroupOf H with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  set S' : Sylow 2 H := S.subtype hSH with hS'
  set C : Subgroup H := Subgroup.centralizer (K' : Set H) with hC
  have : C.Normal := Subgroup.normal_centralizer
  set π : H →* H ⧸ C := QuotientGroup.mk' C with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C
  set SW : Sylow 2 (H ⧸ C) := S'.mapSurjective hπ with hSW
  set LW : Subgroup (H ⧸ C) := K'.map π with hLW
  let eK : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  have : IsSimpleGroup K' := eK.isSimpleGroup
  have hK'nonab : ∃ a b : K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnonab
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    simpa using congrArg eK h
  have hKC : ∀ x : H, x ∈ K' → x ∈ C → x = 1 := by
    intro x hxK hxC
    have hmem : (⟨x, hxK⟩ : K') ∈ Subgroup.center K' := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
    rw [center_eq_bot_of_isSimpleGroup hK'nonab, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set ψ : K' →* H ⧸ C := π.comp K'.subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact Subtype.ext (hKC x x.2 hx)
  have hψrange : ψ.range = LW := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  let eL : LW ≃* K :=
    (MulEquiv.subgroupCongr hψrange).symm.trans ((MonoidHom.ofInjective hψinj).symm.trans eK)
  have : IsSimpleGroup LW := eL.isSimpleGroup
  have hLWnonab : ∃ a b : LW, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnonab
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    simpa using congrArg eL h
  have : LW.Normal := hK'n.map π hπ
  have hCW : Subgroup.centralizer (LW : Set (H ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨h, rfl⟩ := hπ w
    rw [Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := (Subgroup.mem_centralizer_iff.mp hw) (π k) ⟨k, hk, rfl⟩
    have hc1 : h * k * h⁻¹ * k⁻¹ ∈ C := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπdef]
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    have hc2 : h * k * h⁻¹ * k⁻¹ ∈ K' := K'.mul_mem (hK'n.conj_mem k hk h) (K'.inv_mem hk)
    have h2 := hKC _ hc2 hc1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hsup : LW ⊔ (SW : Subgroup (H ⧸ C)) = ⊤ := by
    rw [hSW, Sylow.coe_mapSurjective, hLW, ← Subgroup.map_sup, hS', Sylow.coe_subtype, hK',
      ← Subgroup.subgroupOf_sup hKH hSH, ← hH, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ hπ]
  have hSWab : IsMulCommutative (SW : Subgroup (H ⧸ C)) := by
    rw [hSW, Sylow.coe_mapSurjective]
    have : IsMulCommutative (S' : Subgroup H) := by
      rw [hS', Sylow.coe_subtype]
      have := hY S
      exact Subgroup.comap_injective_isMulCommutative (S : Subgroup Y) H.subtype_injective
    exact Subgroup.map_isMulCommutative _ _
  have hmain := sylow_le_of_centralizer_eq_bot SW hSWab LW hLWnonab hCW hsup
  intro s hs
  have hs' : (⟨s, hSH hs⟩ : H) ∈ (S' : Subgroup H) := by
    rw [hS', Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hs
  have hmem : π ⟨s, hSH hs⟩ ∈ LW := by
    apply hmain
    rw [hSW, Sylow.coe_mapSurjective]
    exact ⟨_, hs', rfl⟩
  obtain ⟨k', hk', hk'eq⟩ := hmem
  have hkc : k'⁻¹ * ⟨s, hSH hs⟩ ∈ C := QuotientGroup.eq.mp hk'eq
  refine ⟨(k' : Y), Subgroup.mem_subgroupOf.mp hk', ?_⟩
  intro x hx
  have h' := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hkc) ⟨x, hKH hx⟩
    (Subgroup.mem_subgroupOf.mpr hx))
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h'
  calc s * x * s⁻¹ = (k' : Y) * ((k' : Y)⁻¹ * s * x) * s⁻¹ := by group
    _ = (k' : Y) * (x * ((k' : Y)⁻¹ * s)) * s⁻¹ := by rw [h']
    _ = (k' : Y) * x * (k' : Y)⁻¹ := by group

end CFSG.Walter
