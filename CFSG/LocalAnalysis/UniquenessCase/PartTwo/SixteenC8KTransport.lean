module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8PropA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma c8k_mem_comap_comm_iff {G H : Type*} [Group G] [Group H] {π : G →* H}
    (hπ : Function.Surjective π) {Oh Zh : Subgroup H} {γ : G} :
    (∀ x ∈ Oh.comap π, γ * x * γ⁻¹ * x⁻¹ ∈ Zh.comap π) ↔
      ∀ y ∈ Oh, π γ * y * (π γ)⁻¹ * y⁻¹ ∈ Zh := by
  constructor
  · intro hc y hy
    obtain ⟨x, rfl⟩ := hπ y
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hc x hy
  · intro hc x hx
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hc (π x) hx

private lemma c8k_mem_comap_inv_iff {G H : Type*} [Group G] [Group H] {π : G →* H}
    (hπ : Function.Surjective π) {Oh Zh : Subgroup H} {γ : G} :
    (∀ x ∈ Oh.comap π, γ * x * γ⁻¹ * x ∈ Zh.comap π) ↔
      ∀ y ∈ Oh, π γ * y * (π γ)⁻¹ * y ∈ Zh := by
  constructor
  · intro hc y hy
    obtain ⟨x, rfl⟩ := hπ y
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hc x hy
  · intro hc x hx
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hc (π x) hx

private lemma c8k_map_invariant {G H : Type*} [Group G] [Group H] {π : G →* H}
    (hπ : Function.Surjective π) {W : Subgroup G}
    (h : ∀ γ : G, ∀ w ∈ W, γ * w * γ⁻¹ ∈ W) :
    ∀ γ' : H, ∀ w' ∈ W.map π, γ' * w' * γ'⁻¹ ∈ W.map π := by
  intro γ' w' hw'
  obtain ⟨γ, rfl⟩ := hπ γ'
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
  exact Subgroup.mem_map.2 ⟨γ * w * γ⁻¹, h γ w hw, by rw [map_mul, map_mul, map_inv]⟩

theorem c8k_nat_of_hat {Γ : Type} [Group Γ] [Finite Γ] {d : Γ}
    {ρ : (Γ ⧸ CFSG.pCore 2 Γ) →* ↥(StatedSL 2 (ZMod 7))}
    {Oh Zh : Subgroup (Γ ⧸ CFSG.pCore 2 Γ)}
    (h : C8HatNat (Γ ⧸ CFSG.pCore 2 Γ) (d : Γ ⧸ CFSG.pCore 2 Γ) ρ Oh Zh) :
    C8KNat Γ d (ρ.comp (QuotientGroup.mk' (CFSG.pCore 2 Γ)))
      (Oh.comap (QuotientGroup.mk' (CFSG.pCore 2 Γ)))
      (Zh.comap (QuotientGroup.mk' (CFSG.pCore 2 Γ))) := by
  let π : Γ →* Γ ⧸ CFSG.pCore 2 Γ := QuotientGroup.mk' (CFSG.pCore 2 Γ)
  let O : Subgroup Γ := Oh.comap π
  let Z : Subgroup Γ := Zh.comap π
  let ρ' : Γ →* ↥(StatedSL 2 (ZMod 7)) := ρ.comp π
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = CFSG.pCore 2 Γ := QuotientGroup.ker_mk' _
  have hqZ : CFSG.pCore 2 Γ ≤ Z := by
    intro x hx
    change x ∈ Zh.comap π
    rw [Subgroup.mem_comap]
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact Zh.one_mem
  refine
    { surj := h.surj.comp hπs
      ker_le := ?_
      normal := h.normal.comap π
      z_normal := h.z_normal.comap π
      q_le := hqZ
      z_le := Subgroup.comap_mono h.z_le
      seven := ?_
      o_le_ker := ?_
      index := ?_
      comm := ?_
      pow := ?_
      ngen := ?_
      cent := ?_
      act_one := ?_
      inv := ?_
      irred := ?_ }
  · have hle : ρ'.ker ≤ (CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pCore 2 Γ)).comap π :=
      Subgroup.comap_mono h.ker_le
    rwa [c8k_pprime_quot Γ] at hle
  · intro x hx
    have hxOh : π x ∈ Oh := hx
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 7) (G := Γ ⧸ CFSG.pCore 2 Γ))
      ⟨π x, h.le_core hxOh⟩
    refine ⟨n, (QuotientGroup.eq_one_iff (x ^ 7 ^ n)).1 ?_⟩
    show π (x ^ 7 ^ n) = 1
    rw [map_pow]
    simpa using congrArg Subtype.val hn
  · intro x hx
    show ρ (π x) = 1
    exact MonoidHom.mem_ker.1 (h.o_le_ker hx)
  · change (Zh.comap π).relIndex (Oh.comap π) = 49
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hπs Oh]
    exact h.index
  · intro x hx y hy
    change π (x * y * x⁻¹ * y⁻¹) ∈ Zh
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h.comm (π x) hx (π y) hy
  · intro x hx
    change π (x ^ 7) ∈ Zh
    rw [map_pow]
    exact h.pow (π x) hx
  · intro H hH hsup
    have hHmap : H.map π ≤ Oh := by
      calc H.map π ≤ O.map π := Subgroup.map_mono hH
        _ = Oh := Subgroup.map_comap_eq_self_of_surjective hπs Oh
    have hsupmap : H.map π ⊔ Zh = Oh := by
      have hc := congrArg (Subgroup.map π) hsup
      rwa [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hπs Zh,
        Subgroup.map_comap_eq_self_of_surjective hπs Oh] at hc
    have hmap := h.ngen (H.map π) hHmap hsupmap
    have hmain : H ⊔ π.ker = O := by
      rw [← Subgroup.comap_map_eq (f := π) (H := H), hmap]
    rw [hker] at hmain
    exact hmain
  · intro n hn hn7 x hx
    have hnker : π n ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      simpa only [MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hn
    have hn7' : ¬ 7 ∣ orderOf (π n) :=
      fun h7 => hn7 (h7.trans (orderOf_map_dvd π n))
    have hc := (Subgroup.mem_centralizer_iff.1 (h.cent (π n) hnker hn7'))
      (π x) (h.le_core hx)
    have hcomm : π n * π x * (π n)⁻¹ * (π x)⁻¹ = 1 := by
      rw [← hc]
      group
    refine (QuotientGroup.eq_one_iff (n * x * n⁻¹ * x⁻¹)).1 ?_
    show π (n * x * n⁻¹ * x⁻¹) = 1
    simpa only [map_mul, map_inv] using hcomm
  · intro γ
    have h1 : ρ' γ = 1 ↔ ρ (π γ) = 1 := Iff.rfl
    rw [h1, h.act_one (π γ)]
    exact (c8k_mem_comap_comm_iff hπs (Oh := Oh) (Zh := Zh) (γ := γ)).symm
  · intro γ hγ1 hγ2
    exact (c8k_mem_comap_inv_iff hπs (Oh := Oh) (Zh := Zh) (γ := γ)).2
      (h.inv (π γ) hγ1 hγ2)
  · intro W hZW hWO hinv
    have hZhW : Zh ≤ W.map π := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hπs Zh]
      exact Subgroup.map_mono hZW
    have hWOh : W.map π ≤ Oh := by
      calc W.map π ≤ O.map π := Subgroup.map_mono hWO
        _ = Oh := Subgroup.map_comap_eq_self_of_surjective hπs Oh
    have hkerW : π.ker ≤ W := by
      rw [hker]
      exact hqZ.trans hZW
    have hW : W = (W.map π).comap π := by
      rw [Subgroup.comap_map_eq (f := π) (H := W)]
      exact (sup_eq_left.2 hkerW).symm
    rcases h.irred (W.map π) hZhW hWOh (c8k_map_invariant hπs hinv) with h | h
    · left
      rw [hW, h]
    · right
      rw [hW, h]

theorem c8k_natural_rep
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) {Γ : Type} [Group Γ]
    [Finite Γ] {B : Subgroup Γ} {d : Γ} (h : C8KCtx Γ B d) :
    ∃ (ρ : Γ →* ↥(StatedSL 2 (ZMod 7))) (O Z : Subgroup Γ), C8KNat Γ d ρ O Z := by
  obtain ⟨ρ, Oh, Zh, hρ⟩ := c8h_natural_rep hSz (c8h_setup_of_kctx h)
  exact ⟨_, _, _, c8k_nat_of_hat hρ⟩

theorem c8k_invol
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) {Γ : Type} [Group Γ] [Finite Γ]
    {B : Subgroup Γ} {d : Γ} (h : C8KCtx Γ B d) :
    ∀ t : Γ, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 Γ :=
  c8k_invol_transfer (c8h_invol hSz (c8h_setup_of_kctx h))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
