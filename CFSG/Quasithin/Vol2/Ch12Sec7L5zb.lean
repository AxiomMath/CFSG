module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5za
public import CFSG.Quasithin.Background.C124AsmPre
public import CFSG.Quasithin.Background.B1More13A

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open CFSG.Open CFSG.Quasithin.ASInputs

theorem odd_index_map {A B : Type*} [Group A] [Group B] (f : A →* B) {K : Subgroup A}
    (hK : Odd K.index) : Odd ((K.map f).subgroupOf f.range).index := by
  have e : (K.map f).subgroupOf f.range = K.map f.rangeRestrict := by
    ext ⟨b, hb⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, Subtype.ext rfl⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨a, ha, congrArg Subtype.val he⟩
  rw [e]
  exact Odd.of_dvd_nat hK (Subgroup.index_map_dvd _ f.rangeRestrict_surjective)

theorem map_map_conj {A B : Type*} [Group A] [Group B] (f : A →* B) (K : Subgroup A) (h : A) :
    (K.map (MulAut.conj h).toMonoidHom).map f = (K.map f).map (MulAut.conj (f h)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

namespace MulHyp

variable {A : Type} [Group A] [Finite A] {W : Type} [CommGroup W] [Finite W]
  [Module (ZMod 2) (Additive W)] {ρ : A →* MulAut W} {Δ₀ : Set (Subgroup W)} {n : ℕ}
  {Δ : Fin n → Set (Subgroup W)}

theorem exists_cComp_map_eq (hM : MulHyp ρ.range Δ₀ Δ)
    (hspan : cCompSpan (⊤ : Subgroup A) = perfectCore (⊤ : Subgroup A)) (i : Fin n) :
    ∃ L' ∈ cComp (⊤ : Subgroup A), L'.map ρ = g31G ρ.range (Δ i) := by
  set G₁ := g31G ρ.range (Δ i) with hG₁
  have hG₁R : G₁ ≤ ρ.range := (hM.g31G_le_g31G i).trans (g31G_le _ _)
  have hG₁P : G₁ ≤ (cCompSpan (⊤ : Subgroup A)).map ρ := by
    rw [hspan, map_perfectCore, ← MonoidHom.range_eq_map]
    exact le_perfectCore_of_perfect hG₁R (hM.perfect i)
  obtain ⟨L', hL', hnc⟩ : ∃ L' ∈ cComp (⊤ : Subgroup A),
      ¬ L'.map ρ ≤ Subgroup.centralizer (G₁ : Set (MulAut W)) := by
    by_contra hall
    push Not at hall
    have hle : G₁ ≤ Subgroup.centralizer (G₁ : Set (MulAut W)) := by
      refine hG₁P.trans ?_
      rw [cCompSpan, (Subgroup.gc_map_comap ρ).l_sSup]
      exact iSup₂_le fun L hL => hall L hL
    obtain ⟨a, b, hab⟩ := hM.nonabelian i
    exact hab (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle b.2) _ a.2))
  have hsub : IsSubnormal (L'.map ρ) ρ.range := by
    have := A3.subnormal_map ρ (subnormal_of_mem_cComp hL')
    rwa [← MonoidHom.range_eq_map] at this
  have hG₁L : G₁ ≤ L'.map ρ := by
    rcases B113.component_le_or_commutator_eq_bot (hM.isComponentOf i) hsub with h | h
    · exact h
    · exfalso
      apply hnc
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact Subgroup.le_centralizer_iff.mp h
  refine ⟨L', hL', le_antisymm ?_ hG₁L⟩
  set L₀ := L' ⊓ G₁.comap ρ with hL₀
  have hL₀sub : IsSubnormal L₀ (⊤ : Subgroup A) := by
    have h1 : IsSubnormal G₁ (L'.map ρ) :=
      A3.subnormal_of_le_of_le (hM.isComponentOf i).2.1 hG₁L (A3.subnormal_le hsub)
    have h2 := A3.subnormal_comap ρ h1
    have h3 := A3.subnormal_inf_right h2 (Subgroup.le_comap_map ρ L')
    rw [inf_comm] at h3
    exact A3.subnormal_trans h3 (subnormal_of_mem_cComp hL')
  have hmap0 : L₀.map ρ = G₁ := by
    refine le_antisymm ((Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _))
      fun g hg => ?_
    obtain ⟨l, hl, rfl⟩ := hG₁L hg
    exact ⟨l, ⟨hl, hg⟩, rfl⟩
  have hmap : (perfectCore L₀).map ρ = G₁ := by
    rw [map_perfectCore, hmap0, perfectCore_eq_self_of_perfect (hM.perfect i)]
  have hne : perfectCore L₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hmap
    obtain ⟨a, b, hab⟩ := hM.nonabelian i
    apply hab
    have ha : (a : MulAut W) = 1 := (Subgroup.eq_bot_iff_forall _).1 hmap.symm _ a.2
    have hb : (b : MulAut W) = 1 := (Subgroup.eq_bot_iff_forall _).1 hmap.symm _ b.2
    exact Subtype.ext (by simp [ha, hb])
  have hle : perfectCore L₀ ≤ L' := (perfectCore_le L₀).trans inf_le_left
  have heq : perfectCore L₀ = L' := by
    by_contra hne'
    exact not_subnormal_of_mem_cComp hL' (lt_of_le_of_ne hle hne') hne (perfectCore_perfect L₀)
      (A3.subnormal_perfectCore hL₀sub)
  rw [← heq, hmap]

omit [Finite A] in
theorem le_ncard_conj (hM : MulHyp ρ.range Δ₀ Δ) {L' : Subgroup A} {i : Fin n}
    (hL : L'.map ρ = g31G ρ.range (Δ i)) {G' : Type} [Group G'] [Finite G'] (f : A →* G')
    (hf : Function.Injective f) : n ≤ (conjSubgroupsBy f.range (L'.map f)).ncard := by
  have hconj : ∀ j : Fin n, ∃ h : A,
      (L'.map (MulAut.conj h).toMonoidHom).map ρ = g31G ρ.range (Δ j) := by
    intro j
    obtain ⟨g, hg, -, hgG⟩ := hM.exists_conj i j
    obtain ⟨h, rfl⟩ := hg
    exact ⟨h, by rw [map_map_conj, hL, hgG]⟩
  choose hh hhh using hconj
  have hmemc : ∀ j, (L'.map (MulAut.conj (hh j)).toMonoidHom).map f ∈
      conjSubgroupsBy f.range (L'.map f) := fun j =>
    ⟨f (hh j), ⟨hh j, rfl⟩, map_map_conj f L' (hh j)⟩
  have hinj : Function.Injective fun j : Fin n =>
      (⟨_, hmemc j⟩ : ↥(conjSubgroupsBy f.range (L'.map f))) := by
    intro j k hjk
    have h1 := congrArg Subtype.val hjk
    simp only at h1
    have h2 := Subgroup.map_injective hf h1
    apply hM.g31G_injective
    simp only
    rw [← hhh j, ← hhh k, h2]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at this

end MulHyp

end CFSG.Quasithin.G31

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem H_le_N (h1222 : Stmt12_2_2) :
    H714 T L V z ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  (s.H_le_Gz h1222).trans (centralizer_le_normalizer_zpowers z)

omit [Finite G] s in
theorem T_le_H : T ≤ H714 T L V z := le_sup_right.trans le_sup_right

theorem tmk_mem_Ht' (h1222 : Stmt12_2_2) (h : ↥(H714 T L V z)) :
    tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h) ∈ Ht T L V z :=
  secMk_mem_secImg h.2

noncomputable def rho
    (h1222 : Stmt12_2_2) : ↥(H714 T L V z) →* MulAut ↥(Ut T L V z) :=
  (conjAct (Ut T L V z)).comp
    (((tmk (Subgroup.zpowers z)).comp (Subgroup.inclusion (s.H_le_N h1222))).codRestrict _
      fun h => s.Ht_le_normalizer h1222 (s.tmk_mem_Ht' h1222 h))

theorem rho_apply
    (h1222 : Stmt12_2_2) (h : ↥(H714 T L V z)) (w : ↥(Ut T L V z)) :
    ((s.rho h1222 h w : ↥(Ut T L V z)) : Gt z) =
      tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h) * (w : Gt z) *
        (tmk (Subgroup.zpowers z) (Subgroup.inclusion (s.H_le_N h1222) h))⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w

theorem range_rho
    (h1222 : Stmt12_2_2) : (s.rho h1222).range = Hs T L V z := by
  ext φ
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨_, s.Ht_le_normalizer h1222 (s.tmk_mem_Ht' h1222 h)⟩, s.tmk_mem_Ht' h1222 h, rfl⟩
  · rintro ⟨⟨y, hyN⟩, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨⟨x, hx⟩, rfl⟩

theorem rho_map_X1
    (h1222 : Stmt12_2_2) {x : G} (hx : x ∈ T) :
    (X1 T L V z).map (s.rho h1222 ⟨x, T_le_H hx⟩).toMonoidHom = X1 T L V z := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
    show ((s.rho h1222 ⟨x, T_le_H hx⟩ w : ↥(Ut T L V z)) : Gt z) ∈
      tildeOf (Subgroup.zpowers z) (V1 T L V)
    obtain ⟨v, hv, hvw⟩ := mem_secImg.1 hw
    rw [s.rho_apply, ← hvw]
    set y : Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
      Subgroup.inclusion (s.H_le_N h1222) ⟨x, T_le_H hx⟩ with hy
    have e : tmk (Subgroup.zpowers z) y * secMk _ _ v * (tmk (Subgroup.zpowers z) y)⁻¹ =
        tmk (Subgroup.zpowers z) (y * v * y⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    refine secMk_mem_secImg ?_
    show x * (v : G) * x⁻¹ ∈ V1 T L V
    exact (Subgroup.mem_normalizer_iff.mp (s.T_le_normalizer_V1 h1222 hx) v).mp hv
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]

theorem odd_index_T :
    Odd (T.subgroupOf (H714 T L V z)).index := by
  have h2 := s.setting.hyp.hyp.sylow.2
  have hdvd : (T.subgroupOf (H714 T L V z)).index ∣ T.index := by
    rw [← Subgroup.relIndex]
    exact Subgroup.relIndex_dvd_index_of_le T_le_H
  rw [Nat.odd_iff]
  have : ¬ 2 ∣ (T.subgroupOf (H714 T L V z)).index := fun h => h2 (dvd_trans h hdvd)
  omega

theorem pCoreOf_H_ne_bot (h1222 : Stmt12_2_2) : pCoreOf 2 (H714 T L V z) ≠ ⊥ := fun hb =>
  s.ne_one (by
    have := s.zpowers_le_pCoreOf h1222 (Subgroup.mem_zpowers z)
    rwa [hb, Subgroup.mem_bot] at this)

theorem card_le_two
    [IsMulCommutative ↥(Ut T L V z)] [Module (ZMod 2) (Additive ↥(Ut T L V z))]
    (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {Δ₀ : Set (Subgroup ↥(Ut T L V z))} {n : ℕ} {Δ : Fin n → Set (Subgroup ↥(Ut T L V z))}
    (hM : MulHyp (s.rho h1222).range Δ₀ Δ) (hn : 0 < n) : n ≤ 2 := by
  have hy := s.setting.hyp.hyp
  have hH := s.pCoreOf_H_ne_bot h1222
  have hspan0 := CFSG.Quasithin.lemma_1_2_1_one hy.qtke hy.simple hy.nonabelian h39 hH
  have hspan : cCompSpan (⊤ : Subgroup ↥(H714 T L V z)) =
      perfectCore (⊤ : Subgroup ↥(H714 T L V z)) := by
    have h1 : perfectCore (⊤ : Subgroup ↥(H714 T L V z)) =
        (perfectCore (H714 T L V z)).subgroupOf (H714 T L V z) := by
      rw [← C124.perfectCore_subgroupOf' (le_refl (H714 T L V z)), Subgroup.subgroupOf_self]
    rw [h1, ← hspan0, cCompSpan_eq_map_subtype (H714 T L V z), Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  obtain ⟨L', hL', hLeq⟩ := hM.exists_cComp_map_eq hspan ⟨0, hn⟩
  have hcard := hM.le_ncard_conj hLeq (H714 T L V z).subtype (Subgroup.subtype_injective _)
  rw [Subgroup.range_subtype] at hcard
  have hLgmem : L'.map (H714 T L V z).subtype ∈ cComp (H714 T L V z) := map_subtype_mem_cComp hL'
  rcases CFSG.Quasithin.lemma_1_2_1_three hy.qtke hy.simple hy.nonabelian h37 h38 hH hLgmem with
    hnorm | ⟨h2, -⟩
  · have hset : conjSubgroupsBy (H714 T L V z) (L'.map (H714 T L V z).subtype) =
        {L'.map (H714 T L V z).subtype} := by
      ext K'
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxN : x ∈ Subgroup.normalizer ((L'.map (H714 T L V z).subtype : Subgroup G) : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLgmem)).mp hnorm hx
        rw [Set.mem_singleton_iff]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
      · rintro rfl
        exact ⟨1, (H714 T L V z).one_mem, by ext x; simp⟩
    rw [hset, Set.ncard_singleton] at hcard
    omega
  · omega


theorem g31V_eq_top
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) :
    g31V (orbitOn (s.rho h1222).range (X1 T L V z)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  set Δ₀ := orbitOn (s.rho h1222).range (X1 T L V z) with hΔ₀
  set N := Subgroup.normalizer (Subgroup.zpowers z : Set G) with hN
  set W := (g31V Δ₀).map (Ut T L V z).subtype with hW
  set P : Subgroup G := (W.comap (tmk (Subgroup.zpowers z))).map N.subtype with hP
  have hUP : U714 T L V z ≤ P := by
    rw [← s.conjClosure_eq h1222]
    refine conjClosure_le fun h hh v hv => ?_
    have hvN : v ∈ N := s.V1_le_N h1222 hv
    have hhN : h ∈ N := s.H_le_N h1222 hh
    have hvU : tmk (Subgroup.zpowers z) ⟨v, hvN⟩ ∈ Ut T L V z :=
      secMk_mem_secImg (le_conjClosure _ _ hv)
    have hvX : (⟨_, hvU⟩ : ↥(Ut T L V z)) ∈ X1 T L V z := by
      rw [Subgroup.mem_subgroupOf]
      exact secMk_mem_secImg hv
    have hY : (X1 T L V z).map (s.rho h1222 ⟨h, hh⟩).toMonoidHom ≤ g31V Δ₀ :=
      le_iSup₂ (f := fun Y (_ : Y ∈ Δ₀) => Y) _ ⟨_, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    have hmem := hY (Subgroup.mem_map_of_mem _ hvX)
    refine ⟨⟨h * v * h⁻¹, N.mul_mem (N.mul_mem hhN hvN) (N.inv_mem hhN)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine ⟨_, hmem, ?_⟩
    show ((s.rho h1222 ⟨h, hh⟩ ⟨_, hvU⟩ : ↥(Ut T L V z)) : Gt z) = _
    rw [s.rho_apply]
    have e : (⟨h * v * h⁻¹, N.mul_mem (N.mul_mem hhN hvN) (N.inv_mem hhN)⟩ : ↥N) =
        Subgroup.inclusion (s.H_le_N h1222) ⟨h, hh⟩ * ⟨v, hvN⟩ *
          (Subgroup.inclusion (s.H_le_N h1222) ⟨h, hh⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  obtain ⟨u, hu, rfl⟩ := mem_secImg.1 hw
  obtain ⟨x, hx, hxu⟩ := hUP hu
  have hxu' : x = u := Subtype.ext hxu
  subst hxu'
  obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_comap.1 hx)
  have : y = ⟨_, hw⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem odd_card
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) {Δ₀ : Set (Subgroup ↥(Ut T L V z))}
    {n : ℕ} {Δ : Fin n → Set (Subgroup ↥(Ut T L V z))} (hM : MulHyp (s.rho h1222).range Δ₀ Δ)
    {i₀ : Fin n} (h0 : X1 T L V z ∈ Δ i₀) : Odd n :=
  hM.odd (S := (T.subgroupOf (H714 T L V z)).map (s.rho h1222))
    (odd_index_map (s.rho h1222) s.odd_index_T) h0 fun g hg => by
      obtain ⟨⟨x, hxH⟩, hx, rfl⟩ := hg
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
      exact s.rho_map_X1 h1222 hx

theorem Hs_eq_top
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    Hs T L V z = ⊤ ∧ 8 ≤ Nat.card ↥(Ut T L V z) := by
  have hV : ∀ v : ↥(Ut T L V z), v ^ 2 = 1 := fun v =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ v.2)
  let _ : Module (ZMod 2) (Additive ↥(Ut T L V z)) :=
    AddCommGroup.zmodModule (n := 2) (two_nsmul_eq_zero hV)
  obtain ⟨n, hn, Δ, h0, hM⟩ := s.exists_mulHyp h1222 hU
  rw [← s.range_rho h1222] at hM
  have h2 := s.card_le_two h1222 h37 h38 h39 hM hn
  obtain ⟨k, hk⟩ := s.odd_card h1222 hM h0
  have h1 : n = 1 := by omega
  have hi : ∀ i : Fin n, i = ⟨0, hn⟩ := fun i => Fin.ext (by have := i.2; omega)
  have hΔ : Δ ⟨0, hn⟩ = orbitOn (s.rho h1222).range (X1 T L V z) := by
    rw [← hM.union]
    ext Y
    simp only [Set.mem_iUnion]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨i, h⟩ => hi i ▸ h⟩
  have htop : g31V (Δ ⟨0, hn⟩) = ⊤ := by
    rw [hΔ]
    exact s.g31V_eq_top h1222
  refine ⟨?_, ?_⟩
  · rw [← s.range_rho h1222, eq_top_iff]
    intro ψ _
    have hψ : ψ ∈ g31Stab (g31V (Δ ⟨0, hn⟩)) := fun v => by
      simp only [htop, Subgroup.mem_top]
    obtain ⟨g, hg, hgv⟩ := hM.autAll ⟨0, hn⟩ (g31Restr (g31V (Δ ⟨0, hn⟩)) ⟨ψ, hψ⟩)
    have hgψ : g = ψ := MulEquiv.ext fun v => by
      have := hgv ⟨v, htop ▸ Subgroup.mem_top v⟩
      simpa [g31Restr_apply] using this
    rw [← hgψ]
    exact ((hM.g31G_le_g31G _).trans (g31G_le _ _)) hg
  · have h8 := hM.eight_le ⟨0, hn⟩
    rwa [htop, Subgroup.card_top] at h8

end CFSG.Quasithin.H13.S127.L715.Set714
