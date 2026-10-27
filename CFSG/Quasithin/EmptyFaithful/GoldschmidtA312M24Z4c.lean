module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesExtra
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Glue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Subs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped Pointwise commutatorElement

theorem V4_le_Z4 : V4 ≤ Z4 := by
  rw [V4, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact evalEltL_mem m24Sg (fun _ hx => Subgroup.subset_closure (List.mem_append_left _ hx)) w

theorem enumV4 :
    EnumOK 24 ((wordG m24Sg V4w).map (tab 24)) V4L V4par := by
  rw [V4g_tab]
  exact V4_check.1

theorem card_V4 : Nat.card V4 = 2 ^ 7 := by
  obtain ⟨-, hcard, -⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective
    (wordG m24Sg V4w) enumV4
  rw [V4, hcard]
  exact V4_check.2.1

theorem V4_fix : ∀ v ∈ V4, ∀ x ∈ L4m, v • x = x := by
  refine fix_of_gens _ L4m (fun g hg x hx => ?_)
  have hgT : tab 24 g ∈ V4T := by rw [← V4g_tab]; exact List.mem_map_of_mem hg
  rw [hact_setset]
  obtain ⟨-, -, -, -, -, -, -, -, -, hfix, -⟩ := V4_check
  exact hfix _ hgT x hx

theorem V4_isExtraspecial : IsExtraspecial2 3 ↥V4 := by
  obtain ⟨-, hlen, hzL, hz1, hzc, hzz, hgsq, hgc, hcen, -⟩ := V4_check
  refine isExtraspecial2_of_enum (gens := wordG m24Sg V4w) enumV4 hzL hz1 hzc hzz
    (by rw [V4g_tab]; exact hgsq) (by rw [V4g_tab]; exact hgc) ?_ (m := 3) (by simpa using hlen)
    (by norm_num)
  rw [V4g_tab]
  exact hcen

theorem rho4_ker [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card rho4.range = 168 ∧ rho4.ker = V4.subgroupOf Z4 := by
  refine ker_eq_of_card rho4 V4_le_Z4
    (fun z hz => listHom_eq_one_of_fix Z4 L4m L4m_nodup Z4_inv z (V4_fix z.1 hz)) (a := 168)
    (b := 2 ^ 7) ?_ card_V4 rho4_dvd (by norm_num) (by norm_num)
  rw [(Z4_eq).1]
  norm_num

theorem rho4_gens_check :
    ∀ i : Fin 5, indTab actSetSet L4m (gens4T.getD i []) = M4tab.getD i [] := by
  decide +kernel

theorem gens4T_getD : ∀ t ∈ gens4T, ∃ i : Fin 5, t = gens4T.getD i [] := by decide

theorem rho4_le_range :
    rho4.range ≤ (Seven.rho Seven.lab8).range := by
  refine range_le_of_gens {g | g ∈ gens4} rho4 _ ?_
  intro g hg
  have ht : tab 24 g ∈ gens4T := by rw [← gens4_tab]; exact List.mem_map_of_mem hg
  obtain ⟨i, hi⟩ := gens4T_getD _ ht
  refine ⟨M4sl i, ?_⟩
  symm
  refine listHom_eq_of_tab actSetSet hact_setset Z4 L4m L4m_nodup Z4_inv ⟨g, _⟩ _ ?_
  show indTab actSetSet L4m (tab 24 g) = tab 7 (Seven.rho Seven.lab8 (M4sl i))
  rw [hi, tab_rho_M4, rho4_gens_check]

theorem rho4_range_eq [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    rho4.range = (Seven.rho Seven.lab8).range :=
  Subgroup.eq_of_le_of_card_ge rho4_le_range (by exact (card_rho8_range.trans rho4_ker.1.symm).le)

theorem rho4_range_perfect [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    perfectCore rho4.range = rho4.range := by
  have := Seven.slThree_isSimple
  rw [rho4_range_eq]
  exact perfectCore_eq_self_of_perfect (Seven.perfect_of_equiv_simple Seven.slThree_nonabelian
    (MonoidHom.ofInjective (Seven.rho_injective Seven.lab8)).symm)

theorem exists_comm_of_enum {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par) {u : G24} {tu t : List ℕ} (htu : tab 24 u = tu)
    (ht : t ∈ L) (hs : ∃ s ∈ L, compTab s tu = compTab (compTab t tu) s) :
    ∃ c : G24, tab 24 c = t ∧ ∃ x ∈ Subgroup.closure {x | x ∈ gens}, ⁅x, u⁆ = c := by
  obtain ⟨-, -, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  obtain ⟨c, -, hc⟩ := hreach t ht
  obtain ⟨s, hs, hsc⟩ := hs
  obtain ⟨x, hx, rfl⟩ := hreach s hs
  refine ⟨c, hc, x, hx, comm_eq_of_mul_eq ?_⟩
  apply eq_of_tab_eq (n := 24)
  rw [tab_mul, tab_mul, tab_mul, htu, hc]
  exact hsc

theorem comm_z_of_enum {gens : List G24} {L : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : EnumOK 24 (gens.map (tab 24)) L par) {u z : G24} {tu zT : List ℕ} (htu : tab 24 u = tu)
    (hzt : tab 24 z = zT)
    (hc : ∀ t ∈ L, ∃ s ∈ L, compTab s tu = compTab (compTab t tu) s ∨
      compTab s tu = compTab (compTab (compTab t zT) tu) s) :
    ∀ v ∈ Subgroup.closure {x | x ∈ gens},
      ∃ x ∈ Subgroup.closure {x | x ∈ gens}, ⁅x, u⁆ = v ∨ ⁅x, u⁆ = v * z := by
  obtain ⟨hmem, -, hreach⟩ := enum_closure (tab 24) tab_one_L tab_mul tab_injective gens h
  intro v hv
  obtain ⟨s, hs, hsc⟩ := hc _ ((hmem v).mp hv)
  obtain ⟨x, hx, rfl⟩ := hreach s hs
  refine ⟨x, hx, ?_⟩
  rcases hsc with hsc | hsc
  · left
    refine comm_eq_of_mul_eq (eq_of_tab_eq (n := 24) ?_)
    rw [tab_mul, tab_mul, tab_mul, htu]
    exact hsc
  · right
    refine comm_eq_of_mul_eq (eq_of_tab_eq (n := 24) ?_)
    rw [tab_mul, tab_mul, tab_mul, tab_mul, htu, hzt]
    exact hsc

theorem V4_le_perfectCore [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z4) : V4 ≤ perfectCore Z4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hV, hc1, hc2, hs1, hs2, hz⟩ := V4_check
  obtain ⟨c₁, hc₁T, hc₁⟩ := exists_comm_of_enum (gens := wordG m24Sg V4w)
    (by rw [V4g_tab]; exact V4_check.1) (tab_u4) hc1 hs1
  obtain ⟨c₂, hc₂T, hc₂⟩ := exists_comm_of_enum (gens := wordG m24Sg V4w)
    (by rw [V4g_tab]; exact V4_check.1) (tab_u4) hc2 hs2
  have hcc : ⁅c₁, c₂⁆ = z0 := by
    refine comm_eq_of_mul_eq ?_
    rw [mul_assoc]
    apply eq_of_tab_eq (n := 24)
    rw [tab_mul, tab_mul, tab_mul, hc₁T, hc₂T, tab_z0]
    exact hz
  have := le_perfectCore_of_commutators_z m24_S_isPGroup hB (hY ▸ V4_le_Z4) (hY ▸ u4_mem)
    (m := 7) (by norm_num) u4_pow hc₁ hc₂ hcc
    (comm_z_of_enum (gens := wordG m24Sg V4w) enumV4 tab_u4 tab_z0 hV)
  rwa [hY] at this

theorem Z4_perfect [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z4) : perfectCore Z4 = Z4 :=
  perfectCore_eq_self_of_le_ker rho4 rho4_range_perfect (V4_le_perfectCore hB hY)
    (le_of_eq rho4_ker.2)

theorem isExt_Z4 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z4) :
    IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hperf := Z4_perfect hB hY
  have hZZ : ⁅Z4, Z4⁆ = Z4 := by
    have := perfectCore_perfect Z4
    rwa [hperf] at this
  obtain ⟨e⟩ := sl3_quotient_of_range rho4 rho4_le_range (rho4_ker.1.ge)
  have hV : IsExtraspecial2 3 ↥rho4.ker := by
    rw [rho4_ker.2]
    exact IsExtraspecial2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe V4_le_Z4).symm V4_isExtraspecial
  exact A312ExtShapes.isExt_extraspecial_sl3_of_lFamily hB hY le_rfl hZZ.le hZZ rho4.ker hV e

end CFSG.Quasithin.A312M24
