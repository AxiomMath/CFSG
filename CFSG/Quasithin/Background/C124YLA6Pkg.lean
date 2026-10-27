module

public import CFSG.Quasithin.Background.C124YLA6Model
public import CFSG.Quasithin.Background.C124YLPack

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

variable {W : Type*} [CommGroup W] [Finite W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  {π : Gam →* ↥Ls}

theorem exists_list_of_le_Pg {H : Subgroup P6} (h : H ≤ Pg) :
    ∃ l : List P6, ∀ g, g ∈ l ↔ g ∈ H := by
  classical
  refine ⟨plist.filter (fun g => decide (g ∈ H)), fun g => ?_⟩
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hg => ⟨h hg, hg⟩⟩

theorem eq_up_Kg (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π)
    {B : Subgroup (MulAut W)} (hB : B ≤ up π Pg) (hw : WOff U Z B) : B = up π Kg := by
  have hφ := phi_injective hinj
  set B' : Subgroup Gam := B.comap (phi π) with hB'
  have hBrange : B ≤ (phi π).range := hB.trans (Subgroup.map_le_range _ _)
  have hBmap : B'.map (phi π) = B := Subgroup.map_comap_eq_self hBrange
  have hB'P : B' ≤ Pg.subgroupOf (alternatingGroup (Fin 6)) := by
    have h1 : B' ≤ (up π Pg).comap (phi π) := Subgroup.comap_mono hB
    rwa [up, Subgroup.comap_map_eq_self_of_injective hφ] at h1
  set H : Subgroup P6 := B'.map (alternatingGroup (Fin 6)).subtype with hH
  have hHsub : H.subgroupOf (alternatingGroup (Fin 6)) = B' :=
    Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin 6)).subtype_injective B'
  have hHA : H ≤ alternatingGroup (Fin 6) := Subgroup.map_subtype_le B'
  have hHP : H ≤ Pg := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_subgroupOf.1 (hB'P hγ)
  have hup : up π H = B := by
    rw [up, hHsub, hBmap]
  obtain ⟨l, hl⟩ := exists_list_of_le_Pg hHP
  rw [← hup] at hw
  obtain ⟨hne, hel, hsq, hcnt⟩ := (woff_up_iff hR hinj hHA hl).1 hw
  have hHK := s1 H hHP hne hel hsq fun l' hl' => by
    rwa [← cntL_congr (l := l) (l' := l') fun g => (hl g).trans (hl' g).symm]
  rw [← hup, hHK]

theorem exists_lift (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) {v : V6} (hv : evenV v = true)
    (hk : ∀ k ∈ klist, fixB k v = true) :
    ∃ u : ↥U, (u : W) ∈ liftFix U Z (up π Kg) ∧ ∀ γ : Gam,
      ((phi π γ) (u : W) * (u : W)⁻¹ ∈ Z ↔ fixB (γ : P6) v = true) := by
  obtain ⟨β, hc, hβ⟩ := coordQuot_of_realizes hR
  have hR' := hR
  obtain ⟨-, -, -, hUst, -, hsec, -⟩ := hR'
  let m : ↥(FFModel.altDn 6).sec := ⟨Multiplicative.ofAdd v, (evenV_iff _).2 hv⟩
  have hmem : (QuotientGroup.mk m : ↥(FFModel.altDn 6).sec ⧸
      (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) ∈
        fixImg U Z β ((Kg.subgroupOf (alternatingGroup (Fin 6))).map (Ls.subtype.comp π)) := by
    refine (mem_fixImg_model hc hβ hsec hUst _ m).2 fun (γ : Gam) hγ => ?_
    exact (fix_iff (γ : P6) (Multiplicative.ofAdd v)).2 (hk _ (Subgroup.mem_subgroupOf.1 hγ))
  obtain ⟨u, hu, hb⟩ := mem_fixImg.1 hmem
  refine ⟨u, mem_liftFix.2 ⟨u.2, hb⟩, fun γ => ?_⟩
  have h1 := comm_mem_iff_model hc hβ hsec γ u m (hUst (π γ) u u.2) hu
  exact h1.trans (fix_iff (γ : P6) (Multiplicative.ofAdd v))

theorem cent_up (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) {x : MulAut W} (hx : x ∈ Ls)
    (hfix : ∀ u ∈ liftFix U Z (up π Kg), x u * u⁻¹ ∈ Z) : x ∈ up π Kg := by
  obtain ⟨g, hg⟩ : ∃ g : Gam, π g = ⟨x, hx⟩ := hR.1 ⟨x, hx⟩
  have hxg : phi π g = x := congrArg Subtype.val hg
  have key : ∀ v : V6, evenV v = true → (∀ k ∈ klist, fixB k v = true) →
      fixB (g : P6) v = true := by
    intro v hv hk
    obtain ⟨u, hu, h⟩ := exists_lift hR hv hk
    exact (h g).1 (by rw [hxg]; exact hfix _ hu)
  obtain ⟨he1, he2, he3⟩ := even_vectors
  have hK := fun k hk => fixed_vectors k hk
  have hmem := cent_dec (g : P6) (Equiv.Perm.mem_alternatingGroup.1 g.2)
    (key e01 he1 fun k hk => (hK k hk).1) (key e25 he2 fun k hk => (hK k hk).2.1)
    (key e34 he3 fun k hk => (hK k hk).2.2)
  exact mem_up.2 ⟨g, memP_iff.1 hmem, hxg⟩

theorem moves_up (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) :
    ∃ u ∈ liftFix U Z (up π Kg), ∃ y ∈ up π Yg, y u * u⁻¹ ∉ Z := by
  obtain ⟨he1, -, -⟩ := even_vectors
  obtain ⟨u, hu, h⟩ := exists_lift hR he1 fun k hk => (fixed_vectors k hk).1
  have hy : (swap 0 2 * swap 4 5 : P6) ∈ alternatingGroup (Fin 6) := Yg_le_A6 witY_moves
  refine ⟨u, hu, phi π ⟨_, hy⟩, mem_up.2 ⟨⟨_, hy⟩, witY_moves, rfl⟩, fun hZ => ?_⟩
  have := (h ⟨_, hy⟩).1 hZ
  rw [moves_dec] at this
  exact Bool.false_ne_true this

theorem sylow_K_Y (hinj : Function.Injective π) : IsSylowTwoOf (up π Kg) (up π Yg) := by
  refine ⟨up_mono Kg_le_Yg, IsPGroup.of_card (n := 2) ?_, ?_⟩
  · rw [card_up hinj Kg_le_A6, card_Kg]
    norm_num
  · have h := Subgroup.index_mul_card ((up π Kg).subgroupOf (up π Yg))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (up_mono (π := π) Kg_le_Yg)).toEquiv,
      card_up hinj Kg_le_A6, card_Kg, card_up hinj Yg_le_A6, card_Yg] at h
    omega

theorem sylow_P (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π) :
    IsSylowTwoOf (up π Pg) Ls := by
  refine ⟨up_le_Ls Pg, IsPGroup.of_card (n := 3) ?_, ?_⟩
  · rw [card_up hinj Pg_le_A6, card_Pg]
    norm_num
  · have h := Subgroup.index_mul_card ((up π Pg).subgroupOf Ls)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (up_le_Ls (π := π) Pg)).toEquiv,
      card_up hinj Pg_le_A6, card_Pg, card_Ls hR hinj] at h
    omega

theorem gen_up (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) :
    Ls = up π Yg ⊔ (Ls ⊓ Subgroup.normalizer (up π Kg : Set (MulAut W))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg⟩ : ∃ g : Gam, π g = ⟨x, hx⟩ := hR.1 ⟨x, hx⟩
    have hxg : phi π g = x := congrArg Subtype.val hg
    have hg' : g ∈ Ygam ⊔ Subgroup.normalizer (Kgam : Set Gam) := by
      rw [gen_Gam]
      exact Subgroup.mem_top g
    rw [← hxg]
    have hmap : (Ygam ⊔ Subgroup.normalizer (Kgam : Set Gam)).map (phi π) =
        up π Yg ⊔ (Subgroup.normalizer (Kgam : Set Gam)).map (phi π) := Subgroup.map_sup _ _ _
    have hmem := Subgroup.mem_map_of_mem (phi π) hg'
    rw [hmap] at hmem
    have hN : (Subgroup.normalizer (Kgam : Set Gam)).map (phi π) ≤
        Ls ⊓ Subgroup.normalizer (up π Kg : Set (MulAut W)) := by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      refine ⟨(π n).2, Subgroup.mem_normalizer_fintype fun k hk => ?_⟩
      obtain ⟨κ, hκ, rfl⟩ := mem_up.1 hk
      have hκ' : κ ∈ Kgam := Subgroup.mem_subgroupOf.2 hκ
      have := (Subgroup.mem_normalizer_iff.1 hn κ).1 hκ'
      exact mem_up.2 ⟨n * κ * n⁻¹, Subgroup.mem_subgroupOf.1 this, by simp [map_mul, map_inv]⟩
    exact (sup_le_sup_left hN (up π Yg)) hmem
  · exact sup_le (up_le_Ls Yg) inf_le_left

theorem sl2_up (hinj : Function.Injective π) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(up π Yg) ≃* SL(2, F)) := by
  obtain ⟨F, iF, fF, hF, ⟨e⟩⟩ := Yg_equiv_sl2
  refine ⟨F, iF, fF, hF, ⟨?_⟩⟩
  exact ((Subgroup.equivMapOfInjective _ _ (phi_injective hinj)).symm.trans
    (Subgroup.subgroupOfEquivOfLe Yg_le_A6)).trans e

theorem package (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π) :
    Package Ls Ls U Z (up π Kg) (up π Yg) := by
  have hwoff : WOff U Z (up π Kg) := by
    refine (woff_up_iff hR hinj Kg_le_A6 (l := klist) fun g => Iff.rfl).2
      ⟨Kg_ne_bot, Kg_comm, Kg_sq, ?_⟩
    rw [cntL_klist, card_Kg]
  exact ⟨up_le_Ls Kg, hwoff, tight_up hR hinj,
    fun x hx _ _ hfix => cent_up hR hx hfix, up_le_Ls Yg, sylow_K_Y hinj, sl2_up hinj,
    moves_up hR, gen_up hR⟩

end CFSG.Quasithin.C124.YL.A6
