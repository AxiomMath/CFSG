module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827B
public import CFSG.Quasithin.Vol2.Ch8Sec2L828D
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section L827F

theorem not_isSolvable_alt6_827 : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 6)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  intro hs
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  have ha : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have hb : Equiv.swap (1 : Fin 6) 2 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have h := congrArg Subtype.val (hc ⟨_, ha⟩ ⟨_, hb⟩)
  simp only [MulMemClass.mk_mul_mk] at h
  revert h
  decide

theorem false_of_code24_827 {Γ W : Type} [Group Γ] [Finite Γ] [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 16) (ψ : Γ →* MulAut W)
    {X₆ : Subgroup (MulAut W)} (hX₆ : AlternatingNatural X₆ ⊤ ⊥ 6) (hX₆ψ : X₆ ≤ ψ.range)
    {s : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s)
    (π : Γ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s))
    (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker) : False := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  have : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    fun f f' h => MulEquiv.ext (congrFun h)
  have hX₆ne := ne_bot_of_alternatingNatural_828 (Or.inr rfl) hX₆
  obtain ⟨πA₀, hπAs₀, -⟩ := hX₆
  let πA : ↥(alternatingGroup (Fin 6)) →* ↥X₆ := πA₀
  have hπAs : Function.Surjective πA := hπAs₀
  have hA6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hπAi : Function.Injective πA := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal πA.ker with h | h
    · exact h
    · exfalso
      apply hX₆ne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨γ, hγ⟩ := hπAs ⟨x, hx⟩
      have h1 : γ ∈ πA.ker := h ▸ Subgroup.mem_top γ
      rw [MonoidHom.mem_ker, hγ] at h1
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h1
  have hX₆s : ¬ Group.IsSolvable ↥X₆ := fun h =>
    not_isSolvable_alt6_827 (Group.isSolvable_of_isSolvable_injective hπAi)
  have hX₆c : Nat.card ↥X₆ = 360 := by
    rw [← Nat.card_congr (Equiv.ofBijective πA ⟨hπAi, hπAs⟩), Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
    decide
  have hcs : Nat.card (ZMod s) = s := Nat.card_zmod s
  have hP : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 (K := ZMod s) 2 le_rfl
      (Or.inr (by rw [hcs]; omega)) (Or.inr (by rw [hcs]; omega))
  set R := π.ker.map ψ with hRdef
  have hRs : Group.IsSolvable ↥R := Group.isSolvable_of_surjective (ψ.subgroupMap_surjective _)
  have hRle : R ≤ ψ.range := Subgroup.map_le_range ψ π.ker
  have hkk : ψ.ker ≤ π.ker := by
    by_contra hnle
    have hnorm : (ψ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
    have htop : ψ.ker.map π = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map π) with h | h
      · exfalso
        apply hnle
        intro k hk
        have : π k ∈ ψ.ker.map π := ⟨k, hk, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this
      · exact h
    apply hX₆s
    have hle : X₆ ≤ R := by
      intro x hx
      obtain ⟨g, rfl⟩ := hX₆ψ hx
      have hg : π g ∈ ψ.ker.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k⁻¹ * g, MonoidHom.mem_ker.mpr ?_, ?_⟩
      · rw [map_mul, map_inv, hkg, inv_mul_cancel]
      · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := Subgroup.card_ker_mul_card_of_surjective hπ
  have h3 : Nat.card ↥π.ker = Nat.card ↥ψ.ker * Nat.card ↥R := by
    have h := Subgroup.card_ker_mul_card_range (ψ.comp π.ker.subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    rw [← h]
    congr 1
    have hk : (ψ.comp π.ker.subtype).ker = ψ.ker.subgroupOf π.ker := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
        Subgroup.coe_subtype]
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkk).toEquiv
  have hkpos : 0 < Nat.card ↥ψ.ker := Nat.card_pos
  have hY : Nat.card ↥ψ.range =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) * Nat.card ↥R := by
    have e : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥ψ.ker *
        (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) * Nat.card ↥R) := by
      rw [h1, ← h2, h3]
      ring
    exact Nat.eq_of_mul_eq_mul_left hkpos e
  have hdis : ∀ x ∈ X₆, x ∈ R → x = 1 := by
    set N₆ := R.subgroupOf X₆ with hN₆
    have hN₆n : N₆.Normal := by
      refine ⟨fun n hn x => ?_⟩
      rw [hN₆, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨g, hg⟩ := hX₆ψ x.2
      obtain ⟨k, hk, hkn⟩ := hn
      refine ⟨g * k * g⁻¹, π.normal_ker.conj_mem k hk g, ?_⟩
      rw [map_mul, map_mul, map_inv, hg, hkn]
      rfl
    have hMn : (N₆.comap πA).Normal := hN₆n.comap πA
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₆.comap πA) with h | h
    · intro x hx hxR
      obtain ⟨γ, hγ⟩ := hπAs ⟨x, hx⟩
      have hγM : γ ∈ N₆.comap πA := by
        rw [Subgroup.mem_comap, hγ, hN₆, Subgroup.mem_subgroupOf]
        exact hxR
      rw [h, Subgroup.mem_bot] at hγM
      rw [hγM, map_one] at hγ
      exact (congrArg Subtype.val hγ).symm
    · exfalso
      apply hX₆s
      have hle : X₆ ≤ R := by
        intro x hx
        obtain ⟨γ, hγ⟩ := hπAs ⟨x, hx⟩
        have hγM : γ ∈ N₆.comap πA := h ▸ Subgroup.mem_top γ
        rw [Subgroup.mem_comap, hγ, hN₆, Subgroup.mem_subgroupOf] at hγM
        exact hγM
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
  let f : ↥X₆ × ↥R → ↥ψ.range := fun xr =>
    ⟨(xr.1 : MulAut W) * xr.2, ψ.range.mul_mem (hX₆ψ xr.1.2) (hRle xr.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨x, r⟩ ⟨x', r'⟩ hxr
    have he : (x : MulAut W) * r = x' * r' := congrArg Subtype.val hxr
    have h1 : (x' : MulAut W)⁻¹ * x = r' * (r : MulAut W)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he, mul_inv_cancel_right]
    have h2 := hdis _ (X₆.mul_mem (X₆.inv_mem x'.2) x.2)
      (h1 ▸ R.mul_mem r'.2 (R.inv_mem r.2))
    have hx : x = x' := Subtype.ext (inv_mul_eq_one.mp h2).symm
    subst hx
    have hr : r = r' := Subtype.ext (mul_left_cancel he)
    rw [hr]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hX₆c, hY] at hle
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have h360 : 360 ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :=
    Nat.le_of_mul_le_mul_right hle hRpos
  have hodd : Odd s := hs.odd_of_ne_two (by omega)
  have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) =
      s * (s ^ 2 - 1) / 2 := by
    have h := CFSG.GorensteinWalter.psl2_card_formula (ZMod s)
      ⟨s, 1, hs, hodd, le_rfl, by rw [hcs, pow_one]⟩
    rw [hcs] at h
    exact h
  have h2s : 2 ∣ s ^ 2 - 1 := by
    have he : Even (s ^ 2 - 1) := Nat.Odd.sub_odd (hodd.pow) odd_one
    exact even_iff_two_dvd.mp he
  have hsP : s ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) := by
    rw [hPSL, Nat.mul_div_assoc _ h2s]
    exact dvd_mul_right s _
  have hPd : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) ∣ 20160 := by
    rw [← card_mulAut_827 (fun a b => mul_comm a b) hW2 hW]
    exact (Dvd.intro _ hY.symm).trans (Subgroup.card_subgroup_dvd_card ψ.range)
  rcases prime_dvd_20160_827 hs (hsP.trans hPd) with rfl | rfl | rfl | rfl
  · omega
  · omega
  · rw [hPSL] at h360
    norm_num at h360
  · rw [hPSL] at h360
    norm_num at h360

end L827F

end CFSG.Quasithin.H13
