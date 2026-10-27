module

public import CFSG.Quasithin.Vol2.Ch9KGFFSpNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.Quasithin.Vol2.Ch9KGFFC

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open hiding StatedSp StatedProj
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative

section Cmp

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {X : Type} [Group X] [Finite X]

theorem cmp_parab
    (h314 : A314Facts) (hc : FFB.CmpHyp L X) {T B : Subgroup Q} (h : A314Statement T B L)
    (hBL : B < L) (hX : ¬ IsAlt 7 X) : ∃ P, IsMaxParabolic2 L P ∧ B = perfectCore P := by
  obtain ⟨h13, h14⟩ := A7.not_a314_nonquasi hBL hc.quasi hc.center_odd
  unfold A314Statement at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13' | h14'
  · obtain ⟨-, -, -, hP⟩ := h1
    exact hP
  · obtain ⟨-, hL, -⟩ := h2
    exact (hX (hc.cmp_two hL)).elim
  · obtain ⟨-, hL⟩ := h3
    exact (hc.false_of_cmp_three h314 hL).elim
  · obtain ⟨-, ⟨s, hL⟩, -⟩ := h4
    cases s
    · exact (hc.false_of_cmp_three_five (Or.inr hL)).elim
    · exact (hc.false_of_cmp_three_five (Or.inl hL)).elim
  · obtain ⟨-, hL, -⟩ := h5
    exact (hc.false_of_cmp_three_five (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h6
    exact (hc.false_of_cmp_sporadic (Or.inl hL)).elim
  · obtain ⟨-, -, -, hL⟩ := h7
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inl hL))).elim
  · obtain ⟨-, hL, -⟩ := h8
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inl hL)))).elim
  · obtain ⟨-, hL, -⟩ := h9
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inr (Or.inl hL))))).elim
  · obtain ⟨-, -, hL⟩ := h10
    exact (hc.false_of_cmp_sporadic (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))).elim
  · obtain ⟨-, hL, -⟩ := h11
    exact (hc.false_of_cmp_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))))).elim
  · obtain ⟨-, -, hL, -⟩ := h12
    exact (hc.false_of_cmp_sporadic
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL))))))).elim
  · exact (h13 h13'.2).elim
  · obtain ⟨-, p, hp, -, hp8, hL⟩ := h14'
    exact (h14 p hp (by omega) hL).elim

end Cmp

section Parab

variable {G : Type} [Group G] [Finite G]

theorem exists_parab_of_sp44
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56)
    {Y T K KY U : Subgroup G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)))
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) (hSp : IsPSp4 2 2 (O2Q KY)) :
    ∃ P, IsMaxParabolic2 (modO2Image Y KY) P ∧ modO2Image Y K = perfectCore P := by
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hqbar := isQuasisimple_modO2Image h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY
    hred hJ hnK hKU
  obtain ⟨hlt', h314bar⟩ := FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA5 hKYc hlt
  obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
  have hqKY : CFSG.IsQuasisimple (O2Q KY) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqbar
  obtain ⟨hqA, hlist, h60, π, hπ⟩ := autOn_facts' h56 hSQ hT hlt.le hKYc hYKY hred
    (perfect_of_mem_cComp hKl) hA5 hJ hKU hqKY
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hqKY
  set π' : ↥(modO2Image Y KY) →* ↥(autOn KY U) := π.comp e.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπ.comp e.symm.surjective
  have hne : π'.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπ's a
    obtain ⟨y, rfl⟩ := hπ's b
    have hx : x ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π'.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  have hker : π'.ker ≤ Subgroup.center ↥(modO2Image Y KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqbar inferInstance).resolve_left hne
  have hc : FFB.CmpHyp (modO2Image Y KY) ↥(autOn KY U) :=
    { quasi := hqbar
      center_odd := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact hodd
      map := ⟨π', hπ's, hker, hne⟩
      list := hlist
      quasiX := hqA
      dvd60 := h60 }
  have hcard := (sp44_facts hKYc hYKY hred hqA hSp).2.1
  have hX : ¬ IsAlt 7 ↥(autOn KY U) := by
    rintro ⟨e7⟩
    have h7 := Nat.card_congr e7.toEquiv
    rw [hcard, card_alternatingGroup1527d 7 (by norm_num)] at h7
    exact absurd h7 (by decide)
  exact cmp_parab h314 hc h314bar hlt' hX

end Parab

section Transport

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_subgroupOf_of_le {H M : Subgroup G} (hHM : H ≤ M) :
    perfectCore (H.subgroupOf M) = (perfectCore H).subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hHM,
    Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le H).trans hHM)]

omit [Finite G] in
theorem map_psi_modO2Image {Y K KY U : Subgroup G} (hKYY : KY ≤ Y) (hKKY : K ≤ KY)
    (hred : IsTwoReducedIn Y U) :
    ((modO2Image Y K).subgroupOf (modO2Image Y KY)).map (psi hKYY hred) =
      (autOn K U).subgroupOf (autOn KY U) := by
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨⟨k, hkY⟩, hk, hky⟩ := hy
    replace hk : k ∈ K := hk
    have hyb : y = barMap hKYY ⟨k, hKKY hk⟩ := Subtype.ext hky.symm
    rw [hyb, psi_barMap]
    exact Setup.mem_autOn_iff.mpr ⟨⟨k, hKYN (hKKY hk)⟩, hk, rfl⟩
  · intro hx
    obtain ⟨g, hgK, hgx⟩ := Setup.mem_autOn_iff.mp hx
    refine ⟨barMap hKYY ⟨g, hKKY hgK⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨g, hKYY (hKKY hgK)⟩, hgK, rfl⟩
    · rw [psi_barMap]
      apply Subtype.ext
      exact hgx

theorem exists_conj_of_parab {Y K KY U : Subgroup G} (hSQ : SQTKGroup ↥Y) (hKYc : KY ∈ cComp Y)
    (hlt : K < KY) (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) (hSp : IsPSp4 2 2 (O2Q KY))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k)
    (θ : ↥(StatedSp 2 F) ≃* ↥(autOn KY U)) {P : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)}
    (hP : IsMaxParabolic2 (modO2Image Y KY) P) (hKP : modO2Image Y K = perfectCore P) :
    ∃ (g : StatedSp 2 F) (j : Fin 2), (autOn K U).subgroupOf (autOn KY U) =
      ((perfectCore (Q2 F j)).map (MulAut.conj g).toMonoidHom).map θ.toMonoidHom := by
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  set ψ := psi hKYY hred with hψ
  obtain ⟨e⟩ := FFB.nonempty_o2q_equiv hSQ hKYc hYKY
  obtain ⟨-, F', _, _, hF', ⟨e3⟩⟩ := hSp
  have hF4 : Nat.card F' = 4 := by rw [hF']; norm_num
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F')) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F' 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hF4])))
  have hsimpL : IsSimpleGroup ↥(modO2Image Y KY) := by
    have := hsimp
    exact (e.symm.trans e3).isSimpleGroup
  have hψne : ψ.ker ≠ ⊤ := by
    intro htop
    apply hKU
    intro k hk
    have h1 : barMap hKYY ⟨k, hlt.le hk⟩ ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hψ, psi_barMap] at h1
    have h2 := (InternalSec.mem_ker_autOnHom hKYN ⟨k, hlt.le hk⟩).1 h1
    exact h2
  have hψi : ψ.ker = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker).resolve_right hψne
  set ψe : ↥(modO2Image Y KY) ≃* ↥(autOn KY U) := MulEquiv.ofBijective ψ
    ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hψi, psi_surjective hKYY hred⟩ with hψe
  have hPL : P ≤ modO2Image Y KY := hP.1.1
  set P' : Subgroup ↥(modO2Image Y KY) := P.subgroupOf (modO2Image Y KY) with hP'
  have hP'map : P'.map (modO2Image Y KY).subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar' : IsParabolic2 (⊤ : Subgroup ↥(modO2Image Y KY)) P' := by
    rw [A312.isParabolic2_top_iff, hP'map]
    exact hP.1
  have hne' : P' ≠ ⊤ := by
    intro htop
    apply hP.2.1
    rw [← hP'map, htop, Subgroup.map_top, Subgroup.range_subtype]
  set Pa : Subgroup ↥(StatedSp 2 F) :=
    (P'.map ψe.toMonoidHom).map θ.symm.toMonoidHom with hPa
  have hparPa : IsParabolic2 (⊤ : Subgroup ↥(StatedSp 2 F)) Pa :=
    isParabolic2_top_map_equiv θ.symm (isParabolic2_top_map_equiv ψe hpar')
  have hnePa : Pa ≠ ⊤ :=
    A5.G3.map_ne_top_of_equiv θ.symm (A5.G3.map_ne_top_of_equiv ψe hne')
  have hcore : (perfectCore Pa).map θ.toMonoidHom = (autOn K U).subgroupOf (autOn KY U) := by
    rw [hPa, ← map_perfectCore, ← map_perfectCore, Subgroup.map_map]
    have hid : θ.toMonoidHom.comp θ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hid, Subgroup.map_id, hP', perfectCore_subgroupOf_of_le hPL, ← hKP]
    exact map_psi_modO2Image hKYY hlt.le hred
  rcases sp4_perfectCore_parabolic_conj hF hparPa hnePa with hbot | ⟨g, j, hgj⟩
  · exfalso
    apply hKU
    intro k hk
    have h1 : (InternalSec.autOnHom hKYN ⟨k, hlt.le hk⟩ : ↥(autOn KY U)) ∈
        (autOn K U).subgroupOf (autOn KY U) := by
      rw [Subgroup.mem_subgroupOf]
      exact Setup.mem_autOn_iff.mpr ⟨⟨k, hKYN (hlt.le hk)⟩, hk, rfl⟩
    rw [← hcore, hbot, Subgroup.map_bot, Subgroup.mem_bot] at h1
    exact (InternalSec.mem_ker_autOnHom hKYN ⟨k, hlt.le hk⟩).1 h1
  · exact ⟨g, j, by rw [← hcore, hgj]⟩

end Transport

end CFSG.Quasithin.H13.Ch9.KGFF
