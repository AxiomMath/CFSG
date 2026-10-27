module

public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19S8C
public import CFSG.Quasithin.Recognition.G112M13Concl13
public import CFSG.Quasithin.Recognition.G112A2ModStmts
public import CFSG.Quasithin.Vol2.Ch12Sec8OneTwelve
public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19A

public section

namespace CFSG.Quasithin.G112A2

open CFSG.ASVolI.ChG

theorem g112ConclusionMod_of_faithfulM {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hF : CFSG.ASVolI.ChG.G112FaithfulWithU33M B Γ X) (h8' : ¬ G11.G112Concl8S8 B Γ X) :
    G112ConclusionMod B Γ X ∨ G112ProposedU33 Γ := by
  rcases hF with hF | hF
  · rcases hF with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h8s | h9 | h10 | h11 | h12 | h13'
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h2))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))
    · exact absurd h8s h8'
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (g112Concl13Mod_of_N h13')))))))))))))
  · exact Or.inr hF

end CFSG.Quasithin.G112A2

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem two_ch618M2 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hG : G11.TheoremG112Fix)
    (hGM : CFSG.ASVolI.G_11_2M)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G} (hl : l ∈ lsCh617 T L V)
    (hlH : l ∉ hCh611 T) {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {B : LinearMap.BilinForm (ZMod 2) A} {β : ↥(uCh611 T L V) →* Multiplicative A}
    {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v₁ : A} {Wsp : Submodule (ZMod 2) A}
    (hv₁ : ∀ z : ↥(uCh611 T L V), (z : G) ∈ ch6ZS T L V →
      (z : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β z) = v₁)
    (hW : ∀ a : A, a ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l ∧ Multiplicative.toAdd (β e) = a) :
    (G111Hyp B ρ.range v₁ Wsp (((conjSubgroup (uCh611 T L V) l ⊓
        Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ)
        (((conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf (hCh611 T)).map ρ) ∧
      G11.G112ConclusionFix B ρ.range (((conjSubgroup (uCh611 T L V) l ⊓
        Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ)) ∧
    IsQuotientOfSQTKTauCeti ↥ρ.range ∧
    CFSG.ASVolI.ChG.G112FaithfulWithU33M B ρ.range
      (((conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf
        (hCh611 T)).map ρ) := by
  have S := h.setting_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617 h331 h432 h512 h614 h615 hl hlH
  have hU := h.uA_eq_ch617 h331 h432 h512 h614 h615
  have hNZ := h.normalizer_Z_eq_ch617 h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hHN : hCh611 T ≤ Subgroup.normalizer (uCh611 T L V : Set G) :=
    hCh611_le_normalizer_u T L V
  obtain ⟨z, -, -, d, -, -, -, haS, haZ, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  set a := d⁻¹ * z * d with ha
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [h.inf_centerOf_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt] at this
    exact haZ this
  have hsqtk : IsQuotientOfSQTKTauCeti
      ↥((realHat_ch618 hR).img (Subgroup.normalizer (zCh611 T : Set G))) := by
    have := h.simple
    have hcore := CFSG.QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke
    have hP : pCoreOf 2 (Subgroup.normalizer (zCh611 T : Set G)) ≠ ⊥ := by
      intro hb
      have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 (zCh611 T)
        (IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one]))
      rw [hb, le_bot_iff] at h1
      rw [h1, Subgroup.card_bot] at hZ2
      norm_num at hZ2
    exact L1294.isQuotientOfSQTK_img (realHat_ch618 hR) (hNZ ▸ hHN) (hcore.1 _ hP)
  have key := S.twelve_of_eq hg hU (realHat_ch618 hR)
    (h.four_lt_ch618 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt) haS haZ hG hsqtk
  have hW' : uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) =
      L128A.wA (ch6ZS T L V) (zCh611 T) := (h.wA_eq_ch617 h331 h432 h512 h614 h615).symm
  rw [hW', h.E_eq_ch617 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hg,
    h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
    hNZ] at key
  obtain ⟨-, h111, h112⟩ := key
  have hXH : conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      hCh611 T := inf_le_right.trans (Subgroup.centralizer_le hZZS)
  have hZX : conjSubgroup (centerOf (uCh611 T L V)) l ≤
      conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have := L128A.Setting.rconj_centerOf_le_rconj_wA (ch6ZS T L V) (zCh611 T) l
    rwa [h.X_eq_ch617 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
      hU] at this
  have e1 := realHat_img_self_ch618 hR hHN
  have e2 := realHat_img_ch618 hR hHN hXH
  have e3 := realHat_img_ch618 hR hHN (hZX.trans hXH)
  have e4 : (realHat_ch618 hR).π a = v₁ := by
    rw [realHat_pi_ch618 hR haU]
    exact hv₁ ⟨a, haU⟩ haS haZU
  have e5 := realHat_hat_ch618 hR (E := uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l) Wsp hW
  rw [e1, e2, e3, e4, e5] at h111
  rw [e1, e2] at h112
  have hsqR : IsQuotientOfSQTKTauCeti ↥ρ.range := by
    rw [hNZ, e1] at hsqtk
    exact hsqtk
  exact ⟨⟨h111, h112⟩, hsqR, hGM A B ρ.range v₁ Wsp _ _ h111 hsqR⟩

theorem false_ch619M2
    (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h625 : Stmt6_2_5) (h626 : Stmt6_2_6)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hG : G11.TheoremG112Fix) (hA2M : G112A2.G112ConclA2Mod) (hGM : CFSG.ASVolI.G_11_2M)
    (hS8 : Res6219S8)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) : False := by
  classical
  obtain ⟨z, hzZ, -, d, hdLS, -, -, haS, haZ, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  have hdH : d ∉ hCh611 T := by
    intro hdH
    apply haZ
    have hzd : z * d = d * z := Subgroup.mem_centralizer_iff.mp hdH z hzZ
    have e : d⁻¹ * z * d = z := by
      calc d⁻¹ * z * d = d⁻¹ * (z * d) := by group
        _ = d⁻¹ * (d * z) := by rw [hzd]
        _ = z := by group
    rw [e]
    exact hzZ
  set a := d⁻¹ * z * d with ha
  obtain ⟨hcomm, hZZU, -, -, -, hsq2, hZ2⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  obtain ⟨A, _, _, _, B, β, ρ, hR⟩ := exists_realization_ch619 (hCh611_le_normalizer_u T L V)
    hZZU hZ2 hsq2 (fun x hx y hy => h.comm_mem_ch615 h331 h432 h512 h614 h615 hx hy)
    (fun x hx => by
      have := h.sq_mem_ch615 h331 h432 h512 h614 h615 hx
      rwa [pow_two] at this)
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  have hVZU := h.inf_centerOf_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [hVZU] at this
    exact haZ this
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ zCh611 T, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hv₁ : ∀ w : ↥(uCh611 T L V), (w : G) ∈ ch6ZS T L V →
      (w : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β w) = piA_ch619 hR a := by
    intro w hwS hwZU
    rw [← piA_eq_ch619 hR w.2]
    have hwZ : (w : G) ∉ zCh611 T := fun hwZ => hwZU (hZZU hwZ)
    rw [piA_eq_iff_ch619 hR w.2 haU]
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ haS hwS with e | e | e | e
    · exact absurd (e ▸ (zCh611 T).one_mem) hwZ
    · exact absurd (e ▸ hz₀Z) hwZ
    · rw [e, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [e]
      have hz₀U := hZZU hz₀Z
      have hc : a * z₀ = z₀ * a := Subgroup.mem_centralizer_iff.mp hz₀U.2 a haU
      have e3 : (z₀ * a)⁻¹ * a = z₀⁻¹ := by
        calc (z₀ * a)⁻¹ * a = (a * z₀)⁻¹ * a := by rw [hc]
          _ = z₀⁻¹ := by group
      rw [e3]
      exact Subgroup.inv_mem _ hz₀U
  let Wsp : Submodule (ZMod 2) A :=
    { carrier := {x | ∃ e : ↥(uCh611 T L V),
        (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) d ∧ Multiplicative.toAdd (β e) = x}
      add_mem' := by
        rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
        exact ⟨e * e', Subgroup.mul_mem _ he he', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one]⟩
      smul_mem' := by
        rintro c _ ⟨e, he, rfl⟩
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one, zero_smul]⟩
        · exact ⟨e, he, by rw [one_smul]⟩ }
  have hW : ∀ x : A, x ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) d ∧ Multiplicative.toAdd (β e) = x :=
    fun x => Iff.rfl
  obtain ⟨⟨h111, -⟩, -, hF⟩ := h.two_ch618M2 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hG
    hGM hlt hdLS hdH hR hv₁ hW
  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615 h6210 h6211 h6212 hlt
  have hd4 := h.four_le_finrank_ch619 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR
  have htX := h.mem_map_X_ch619 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hdLS hdH hv
  have hrk := h.finrank_range_ch619 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv hvU
  have hv₁R : piA_ch619 hR a ∈
      LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id) :=
    (h.mem_range_iff_ch619 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv hvU _).mpr
      ⟨a, ⟨haS.1, haU⟩, rfl⟩
  have ha2 := h.isA2_ch619 h331 h432 h512 h614 h615 hR hv
  have hfix := h.fix_ch619 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hlt hR hv hvU haS
    haZ
  have h8' : ¬ G11.G112Concl8S8 B ρ.range (((conjSubgroup (uCh611 T L V) d ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ) := by
    intro h8
    rcases hZZU.lt_or_eq with hZlt | hZeq
    · exact hS8 G T M L V h hlt hZlt d hdLS hdH A B β ρ hR h8
    · exact s8NoTrivialX0 A B ρ.range (piA_ch619 hR a) Wsp _ _ h111 h8
        (h.map_eq_bot_ch619 h331 h432 h512 h614 h615 hR hdLS hZeq.symm)
  have hc := G112A2.g112ConclusionMod_of_faithfulM hF h8'
  obtain ⟨γ, hγ, hγR, hγv⟩ := hA2M A B ρ.range (piA_ch619 hR a) Wsp _ _ h111 hc hd4 _ htX hrk
    hv₁R ha2
  exact hγv (hfix γ hγ hγR)

end Hyp6Sec2

theorem stmt6_2_19Case2_ofM2
    (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h625 : Stmt6_2_5) (h626 : Stmt6_2_6)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hG : G11.TheoremG112Fix) (hA2M : G112A2.G112ConclA2Mod) (hGM : CFSG.ASVolI.G_11_2M)
    (hS8 : Res6219S8) : Stmt6_2_19Case2 := by
  intro G _ _ T M L V h hlt
  exact h.false_ch619M2 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hG hA2M hGM hS8
    hlt

theorem stmt6_2_19Case2_of_a2M2
    (h331 : Stmt3_3_1)
    (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h614 : Stmt6_1_4) (h615 : Stmt6_1_5)
    (h625 : Stmt6_2_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) (hG : G11.TheoremG112Fix) (hA2M : G112A2.G112ConclA2Mod)
    (hGM : CFSG.ASVolI.G_11_2M) : Stmt6_2_19Case2 :=
  stmt6_2_19Case2_ofM2 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hG hA2M hGM
    (res6219S8_of h331 h432 h512 h614 h615 h626 h6210 h6211 h6212)

end CFSG.Quasithin.H13
