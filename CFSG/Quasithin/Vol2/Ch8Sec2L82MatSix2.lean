module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22F
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatOrd3
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatSix
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FSix

public section

namespace CFSG.Quasithin.H13.M22F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open scoped Pointwise

section Core

variable {G : Type} [Group G] [Finite G]

theorem six6i_core_m22f2
    {V L₀ M T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hLM : L₀ ≤ M) (hMN : M ≤ Subgroup.normalizer (L₀ : Set G))
    (hL : CodeHyp22_m22f hV L₀) (hnot : ¬ autOn T V ≤ autOn L₀ V) (hsix : CFSG.Quasithin.H13.Mat.Code22SixNoPerm2_m22f) :
    ∀ F : Subgroup G, F ≤ M → F ≤ Subgroup.normalizer (V : Set G) →
      (∀ x ∈ F, Nat.Coprime (orderOf x) 6) →
      ((F ⊔ T : Subgroup G) : Set G) = (F : Set G) * (T : Set G) →
      F ≤ Subgroup.centralizer (V : Set G) := by
  intro F hFM hFN hcop hset
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  haveI : Finite (MulAut ↥V) := finite_mulAut ↥V
  set K : Subgroup G := M ⊓ Subgroup.normalizer (V : Set G) with hKdef
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hTK : T ≤ K := le_inf hTM hTN
  have hrkT : CFSG.Quasithin.rk ↥T = CFSG.Quasithin.rk G := rk_eq_of_sylowTwo_m22f hT
  have hKle : CFSG.Quasithin.rk ↥K ≤ CFSG.Quasithin.rk G := by
    have := CFSG.Quasithin.rk_add_rkIdx K
    omega
  have hTle : CFSG.Quasithin.rk ↥T ≤ CFSG.Quasithin.rk ↥K := CFSG.Quasithin.rk_mono hTK
  have hrkK : CFSG.Quasithin.rk ↥K = CFSG.Quasithin.rk ↥T := by omega
  have hP : CFSG.Quasithin.rk ↥(T.subgroupOf K) = CFSG.Quasithin.rk ↥K := by
    have hcard : Nat.card ↥(T.subgroupOf K) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
    have h' : CFSG.Quasithin.rk ↥(T.subgroupOf K) = CFSG.Quasithin.rk ↥T := by
      unfold CFSG.Quasithin.rk
      rw [hcard]
    rw [h', hrkK]
  have hrkS : CFSG.Quasithin.rk ↥(autOn T V) = CFSG.Quasithin.rk ↥(autOn M V) := by
    have key := rk_map_eq_range_m22f ((conjAct V).comp (Subgroup.inclusion hKN)) (T.subgroupOf K) hP
    rw [← autOn_eq_map_m22f hTK hKN, ← autOn_eq_range_m22f hKN, autOn_inf_normalizer_m22f] at key
    exact key
  have hset2 : ((autOn F V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) *
      ((autOn T V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) =
      ((autOn F V ⊔ autOn T V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (autOn F V ⊔ autOn T V).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · intro hx
      have hle : autOn F V ⊔ autOn T V ≤ autOn (F ⊔ T) V :=
        sup_le (AutOn.autOn_mono le_sup_left) (AutOn.autOn_mono le_sup_right)
      obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp (hle hx)
      have hn' : (n : G) ∈ (F : Set G) * (T : Set G) := by
        rw [← hset]
        exact hn
      obtain ⟨f, hf, t, ht, hft⟩ := hn'
      refine ⟨conjAct V ⟨f, hFN hf⟩, AutOn.conjAct_mem_autOn_of_mem (hFN hf) hf,
        conjAct V ⟨t, hTN ht⟩, AutOn.conjAct_mem_autOn_of_mem (hTN ht) ht, ?_⟩
      dsimp only
      rw [← map_mul]
      congr 1
      exact Subtype.ext hft
  obtain ⟨e, he⟩ := code22_std hL
  have hIO : IsOver (autOn L₀ V) (Subgroup.normalizer (autOn L₀ V : Set (MulAut ↥V))) :=
    ⟨Subgroup.le_normalizer, le_rfl⟩
  have hLΓ : autOn L₀ V ≤ autOn M V := AutOn.autOn_mono hLM
  have hLneΓ : autOn L₀ V ≠ autOn M V := fun h => hnot ((AutOn.autOn_mono hTM).trans (le_of_eq h.symm))
  have hρX : (rhoC10 mog22 mog22_le_mog22plus).range < (autOn M V).map (CFSG.Quasithin.H.congrHom e) := by
    rw [← he]
    exact lt_of_le_of_ne (Subgroup.map_mono hLΓ)
      (fun h => hLneΓ (Subgroup.map_injective (CFSG.Quasithin.H.congrHom_injective e) h))
  have hX'N : (autOn M V).map (CFSG.Quasithin.H.congrHom e) ≤ (rhoC10 mog22plus le_rfl).range :=
    map_le_of_normalizer hIO he normalizer_rhoC10_mog22 (AutOn.autOn_le_normalizer_autOn hMN)
  have hS'X : (autOn T V).map (CFSG.Quasithin.H.congrHom e) ≤ (autOn M V).map (CFSG.Quasithin.H.congrHom e) :=
    Subgroup.map_mono (AutOn.autOn_mono hTM)
  have hF'X : (autOn F V).map (CFSG.Quasithin.H.congrHom e) ≤ (autOn M V).map (CFSG.Quasithin.H.congrHom e) :=
    Subgroup.map_mono (AutOn.autOn_mono hFM)
  have hrk' : CFSG.Quasithin.rk ↥((autOn T V).map (CFSG.Quasithin.H.congrHom e)) =
      CFSG.Quasithin.rk ↥((autOn M V).map (CFSG.Quasithin.H.congrHom e)) := by
    unfold CFSG.Quasithin.rk
    rw [Subgroup.card_map_of_injective (CFSG.Quasithin.H.congrHom_injective e),
      Subgroup.card_map_of_injective (CFSG.Quasithin.H.congrHom_injective e)]
    unfold CFSG.Quasithin.rk at hrkS
    exact hrkS
  have hcop' : ∀ x ∈ (autOn F V).map (CFSG.Quasithin.H.congrHom e), Nat.Coprime (orderOf x) 6 := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    rw [orderOf_injective (CFSG.Quasithin.H.congrHom e) (CFSG.Quasithin.H.congrHom_injective e) f]
    obtain ⟨g, hg, rfl⟩ := AutOn.mem_autOn_iff.mp hf
    exact Nat.Coprime.coprime_dvd_left (orderOf_conjAct_dvd_m22f (hFN hg)) (hcop g hg)
  have hset' : (((autOn F V).map (CFSG.Quasithin.H.congrHom e) : Subgroup (MulAut W10)) : Set (MulAut W10)) *
      (((autOn T V).map (CFSG.Quasithin.H.congrHom e) : Subgroup (MulAut W10)) : Set (MulAut W10)) =
      ((((autOn F V).map (CFSG.Quasithin.H.congrHom e)) ⊔ ((autOn T V).map (CFSG.Quasithin.H.congrHom e)) :
        Subgroup (MulAut W10)) : Set (MulAut W10)) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · intro hx
      have hle : ((autOn F V).map (CFSG.Quasithin.H.congrHom e)) ⊔ ((autOn T V).map (CFSG.Quasithin.H.congrHom e)) ≤
          ((autOn F V ⊔ autOn T V).map (CFSG.Quasithin.H.congrHom e) : Subgroup (MulAut W10)) :=
        sup_le (Subgroup.map_mono le_sup_left) (Subgroup.map_mono le_sup_right)
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hle hx)
      have hy' : y ∈ ((autOn F V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) *
          ((autOn T V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
        rw [hset2]
        exact hy
      obtain ⟨a, ha, b, hb, hab⟩ := hy'
      exact ⟨CFSG.Quasithin.H.congrHom e a, Subgroup.mem_map_of_mem _ ha,
        CFSG.Quasithin.H.congrHom e b, Subgroup.mem_map_of_mem _ hb, by
          rw [← hab]
          exact (map_mul (CFSG.Quasithin.H.congrHom e) a b).symm⟩
  have hSpAut : IsPGroup 2 ↥(autOn T V) := by
    rw [autOn_eq_map_m22f hTK hKN]
    exact (hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm).map _
  have hSp' : IsPGroup 2 ↥((autOn T V).map (CFSG.Quasithin.H.congrHom e)) := hSpAut.map _
  have hFb : (autOn F V).map (CFSG.Quasithin.H.congrHom e) = ⊥ :=
    hsix _ _ _ hρX hX'N hS'X hSp' hrk' hF'X hcop' hset'
  have hFone : ∀ f : G, f ∈ F → ∀ v ∈ V, f * v * f⁻¹ = v := by
    intro f hf v hv
    have hfN := hFN hf
    have hmem : conjAct V ⟨f, hfN⟩ ∈ autOn F V := AutOn.conjAct_mem_autOn_of_mem hfN hf
    have h1 : CFSG.Quasithin.H.congrHom e (conjAct V ⟨f, hfN⟩) = 1 := by
      have hm := Subgroup.mem_map_of_mem (CFSG.Quasithin.H.congrHom e) hmem
      rw [hFb, Subgroup.mem_bot] at hm
      exact hm
    have h2 : conjAct V ⟨f, hfN⟩ = 1 := by
      apply CFSG.Quasithin.H.congrHom_injective e
      rw [h1, map_one]
    have h3 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h2
    simpa [conjAct_apply_m22f] using h3
  intro f hf
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := hFone f hf v hv
  have key : f * v = v * f := by
    calc f * v = (f * v * f⁻¹) * f := by group
      _ = v * f := by rw [h]
  exact key.symm


end Core

end CFSG.Quasithin.H13.M22F

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.M22F CFSG.Quasithin.H13.Mat

theorem m22Facts822_of_proved
    (hZN : ZNormVStmt_m22f) : M22Facts822 := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot hV
  have hsylow : quasithinIsSylowTwo T := hyp.fsu.sylow
  have hTN₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    (CFSG.Quasithin.B1Red.le_normalizer_conjClosure_sup (T := T) (K := L)).trans' le_sup_left
  have hTNV : T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (CFSG.Quasithin.B1Red.le_normalizer_conjClosure_sup (T := T) (K := I)).trans' le_sup_left
  have hLM : fsuL0 T L ≤ fsuM T L := Subgroup.le_normalizer
  have hMN : fsuM T L ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_rfl
  have hTM : T ≤ fsuM T L := hTN₀
  have hL : CodeHyp22_m22f hV (fsuL0 T L) := hrowM
  have hnotM : ¬ autOn (fsuM T L) (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) :=
    not_le_autOn_of_T_m22f hTM hnot
  refine ⟨qInt_eq_two_m22f hV hTN₀ hL hnot, not_isDualFFInt_m22f hV hTN₀ hL, ?_,
    two_le_qMin_m22f hV hLM hMN hL hnotM, ?_⟩
  ·
    intro F hF hcop hset
    have hFM : F ≤ fsuM T L := hF.trans inf_le_left
    have hFN : F ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      hF.trans (hZN G T L I hyp h731 h821 hc hrow hrowM hnot)
    exact six6i_core_m22f2 hV hsylow hTM hTNV hLM hMN hL hnot code22SixNoPerm2_m22f_proved F hFM
      hFN hcop hset
  ·
    intro X hX hXN hcard k hk
    exact six6iii_img_m22f hV hMN hL code22Ord3Rank6_m22f_proved X (hX.trans inf_le_left) hXN hcard
      k hk

end CFSG.Quasithin.H13
