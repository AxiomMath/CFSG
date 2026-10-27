module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Glue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Subs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

@[expose] def V1w : List (List ℕ) := [[3], [1, 3, 1], [2, 3, 2], [0, 0, 0, 3, 0]]

@[expose] def V1T : List (List ℕ) := V1w.map (wordTab 24 sTL)

@[expose] def V1 : Subgroup G24 := Subgroup.closure {x | x ∈ wordG m24Sg V1w}

theorem V1g_tab : (wordG m24Sg V1w).map (tab 24) = V1T := by
  rw [wordG_tab m24Sg V1w (by simp only [m24Sg_length]; decide), m24Sg_tab]
  rfl

theorem enumV1 : EnumOK 24 V1T (bfsL 24 V1T 200).1 (bfsL 24 V1T 200).2 := by decide +kernel

theorem lenV1 : (bfsL 24 V1T 200).1.length = 16 := by decide +kernel

theorem V1_fixT : ∀ t ∈ V1T, ∀ x ∈ LO, t.getD x x = x := by decide +kernel

theorem V1_le_Z1 : V1 ≤ Z1 := by
  rw [V1, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) w

theorem card_V1 : Nat.card V1 = 16 := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG m24Sg V1w) (by rw [V1g_tab]; exact enumV1)
  rw [V1, hcard]
  exact lenV1

theorem V1_fix : ∀ v ∈ V1, ∀ x ∈ LO, v • x = x := by
  refine fix_of_gens _ LO (fun g hg x hx => ?_)
  have hgT : tab 24 g ∈ V1T := by rw [← V1g_tab]; exact List.mem_map_of_mem hg
  rw [smul_nat]
  exact V1_fixT _ hgT x hx

theorem V1_gens_comm : ∀ g ∈ V1T, ∀ h ∈ V1T, compTab g h = compTab h g := by decide +kernel

theorem V1_gens_sq : ∀ g ∈ V1T, compTab g g = List.range 24 := by decide +kernel

theorem V1_isE2 : IsE2 4 ↥V1 :=
  isE2_of_enum (gens := wordG m24Sg V1w) (by rw [V1g_tab]; exact enumV1)
    (by rw [V1g_tab]; exact V1_gens_comm) (by rw [V1g_tab]; exact V1_gens_sq)
    (lenV1.trans (by norm_num))

theorem V1_comm : ∀ v ∈ V1, ∃ x ∈ V1, ⁅x, y1⁆ = v :=
  comm_surj_of_enum (gens := wordG m24Sg V1w) (by rw [V1g_tab]; exact enumV1) tab_y1
    (by decide +kernel)

theorem rho1_ker [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card rho1.range = 20160 ∧ rho1.ker = V1.subgroupOf Z1 :=
  ker_eq_of_card rho1 V1_le_Z1
    (fun z hz => listHom_eq_one_of_fix Z1 LO LO_nodup Z1_inv z (V1_fix z.1 hz)) (a := 20160)
    (b := 16) (by rw [Z1_eq_Y1.1]) card_V1 rho1_dvd (by norm_num) (by norm_num)

instance : Nontrivial (Fin LO.length) := Fin.nontrivial_iff_two_le.mpr (by decide)

theorem card_alt8 : Nat.card (alternatingGroup (Fin LO.length)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem rho1_range [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    rho1.range = alternatingGroup (Fin LO.length) := by
  exact eq_alt_of_card _ (rho1_ker.1.trans card_alt8.symm)

theorem Z1_perfect [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z1) : perfectCore Z1 = Z1 := by
  refine perfectCore_eq_self_of_ker m24_S_isPGroup hB hY rho1 ?_ V1_le_Z1 (le_of_eq rho1_ker.2)
    y1_mem (m := 5) (by norm_num) y1_pow V1_comm
  rw [rho1_range]
  exact perfectCore_alt (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)

end CFSG.Quasithin.A312M24
