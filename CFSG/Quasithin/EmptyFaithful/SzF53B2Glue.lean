module

public import CFSG.Quasithin.Recognition.F112J2Setup
public import CFSG.Quasithin.EmptyFaithful.SzF53Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53B2Pure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace SzF53B2

section Amalg

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem swap (h : F53Amalgam H M S) : AmalgamHyp (M ⊔ H) M H S where
  gen := sup_comm H M ▸ rfl
  charTwo := h.charTwo_right
  sylow₁ := h.amalgam.sylow₂
  sylow₂ := h.amalgam.sylow₁
  o2_trivial := by rw [sup_comm]; exact h.amalgam.o2_trivial

structure B2Base (H M S : Subgroup G) : Prop where
  amalgam : F53Amalgam H M S
  zb_normal : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G)

structure B2Setup (H M S : Subgroup G) : Prop extends B2Base H M S where
  crit : critDist (M ⊔ H) M H (VZ S M) = 2

namespace B2Base

theorem sylow_M (h : B2Base H M S) : IsSylowTwoOf S M := (swap h.amalgam).sylow₁
theorem sylow_H (h : B2Base H M S) : IsSylowTwoOf S H := (swap h.amalgam).sylow₂

omit [Finite G] in
theorem zb_le_S (S : Subgroup G) :
    quasithinOmegaOneCenter S ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

omit [Finite G] in
theorem zb_le_centralizer (S : Subgroup G) :
    S ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) :=
  Subgroup.le_centralizer_iff.mp ((zb_le_S S).trans inf_le_right)

theorem relIndex_facts (h : B2Base H M S) :
    (pCoreOf 2 M).relIndex M = 6 ∧ (pCoreOf 2 M).relIndex S = 2 ∧ S.relIndex M = 3 := by
  have hSM : S ≤ M := h.sylow_M.1
  have h6 : (pCoreOf 2 M).relIndex M = 6 := F112W.relIndex_pCoreOf_eq_six h.amalgam.quot_right
  have h3 : S.relIndex M = 3 := by
    have := F112J2.relIndex_inf_eq_three (L := M) (S := S)
      (by rw [inf_eq_left.mpr hSM]; exact h.sylow_M) h.amalgam.quot_right
    rwa [inf_eq_left.mpr hSM] at this
  refine ⟨h6, ?_, h3⟩
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 M) S M
    (isSylowTwoOf_pCoreOf_le h.sylow_M) hSM
  rw [h6, h3] at hmul
  omega

theorem normalizer_S (h : B2Base H M S) : ∀ x ∈ M, conjSub x S = S → x ∈ S := by
  intro x hxM hx
  have hSM : S ≤ M := h.sylow_M.1
  have hxN : x ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_of_conjSub_eq hx
  obtain ⟨-, h2, h3⟩ := h.relIndex_facts
  have hle : S ≤ M ⊓ Subgroup.normalizer (S : Set G) := le_inf hSM Subgroup.le_normalizer
  have hmul := Subgroup.relIndex_mul_relIndex S (M ⊓ Subgroup.normalizer (S : Set G)) M hle
    inf_le_left
  rw [h3] at hmul
  have hdvd : (M ⊓ Subgroup.normalizer (S : Set G)).relIndex M ∣ 3 := ⟨_, by rw [← hmul]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  ·
    exfalso
    have hMN : M ≤ Subgroup.normalizer (S : Set G) := fun m hm => by
      have := Subgroup.relIndex_eq_one.mp h1 hm
      exact this.2
    have hSQ : S ≤ pCoreOf 2 M := le_pCoreOf_of_le_normalizer 2 hSM hMN h.sylow_M.2.1
    have := Subgroup.relIndex_eq_one.mpr hSQ
    omega
  · rw [h1] at hmul
    have h1' : S.relIndex (M ⊓ Subgroup.normalizer (S : Set G)) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1' ⟨hxM, hxN⟩

theorem zb_ne_bot (h : B2Base H M S) : quasithinOmegaOneCenter S ≠ ⊥ := by
  have hS2 := h.sylow_M.2.1
  have hSne : S ≠ ⊥ := by
    intro hS
    have h2 := h.relIndex_facts.2.1
    have : S ≤ pCoreOf 2 M := hS ▸ bot_le
    have := Subgroup.relIndex_eq_one.mpr this
    omega
  have : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nontrivial ↥(Subgroup.center ↥S) := hS2.center_nontrivial
  have hcen2 : IsPGroup 2 (Subgroup.center ↥S) := hS2.to_subgroup _
  obtain ⟨n, hn⟩ := hcen2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card ↥(Subgroup.center ↥S) = 1 := by simpa using hn
    have h1 : Subsingleton ↥(Subgroup.center ↥S) := Nat.card_eq_one_iff_unique.mp this |>.1
    exact (not_subsingleton _) h1
  have hdvd2 : 2 ∣ Nat.card ↥(Subgroup.center ↥S) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥S) 2 hdvd2
  have hzS : ((y : ↥S) : G) ∈ S := (y : ↥S).2
  have hzC : ((y : ↥S) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp y.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hz2 : ((y : ↥S) : G) ^ 2 = 1 := by
    have := congrArg (fun t : ↥(Subgroup.center ↥S) => ((t : ↥S) : G)) hy2
    simpa using this
  have hz1 : ((y : ↥S) : G) ≠ 1 := by
    intro h1
    have : y = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [this, orderOf_one] at hy
    omega
  intro hbot
  have hmem : ((y : ↥S) : G) ∈ quasithinOmegaOneCenter S :=
    Subgroup.subset_closure ⟨⟨hzS, hzC⟩, hz2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

theorem le_centralizer_zb (h : B2Base H M S) :
    H ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) := by
  have hSH := h.sylow_H
  have hC : (H ⊓ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G)) = H := by
    refine eq_of_normal_odd_index_perm_five h.amalgam.quot_left inf_le_left ?_ ?_ ?_
    · exact le_normalizer_inf Subgroup.le_normalizer
        (h.zb_normal.trans (normalizer_le_normalizer_centralizer _))
    · exact le_inf ((isSylowTwoOf_pCoreOf_le hSH).trans hSH.1)
        ((isSylowTwoOf_pCoreOf_le hSH).trans (zb_le_centralizer S))
    · intro hd
      exact F7.isSylowTwoOf_odd_relIndex hSH
        (hd.trans (Subgroup.relIndex_dvd_of_le_left H (le_inf hSH.1 (zb_le_centralizer S))))
  intro x hx
  rw [← hC] at hx
  exact hx.2

theorem not_le_normalizer_zb (h : B2Base H M S) :
    ¬ M ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G) := by
  intro hM
  have hSM := h.sylow_M.1
  have hSH := h.sylow_H.1
  have hN : M ⊔ H ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G) :=
    sup_le hM h.zb_normal
  have hZS : quasithinOmegaOneCenter S ≤ S := (zb_le_S S).trans inf_le_left
  have hcore := F112W.coreIn_eq_bot_of_amalgamHyp (swap h.amalgam)
  have : quasithinOmegaOneCenter S ≤ coreIn (M ⊓ H) (M ⊔ H) :=
    le_coreIn (hZS.trans (hSM.trans le_sup_left)) hN (le_inf (hZS.trans hSM) (hZS.trans hSH))
  rw [hcore] at this
  exact h.zb_ne_bot (le_bot_iff.mp this)

omit [Finite G] in
theorem mem_normalizer_zpowers_of_comm {z m : G} (h : m * z = z * m) :
    m ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hmem : m ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (show Commute z m from h.symm) k).eq
  exact Subgroup.centralizer_le_normalizer _ hmem

theorem omegaOneCenter_M (h : B2Base H M S) : quasithinOmegaOneCenter M = ⊥ := by
  have hA := swap h.amalgam
  have hSM := h.sylow_M.1
  unfold quasithinOmegaOneCenter
  rw [eq_bot_iff, Subgroup.closure_le]
  rintro z ⟨⟨hzM, hzC⟩, hz2⟩
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hzQ : z ∈ pCoreOf 2 M := hA.charTwo ⟨hzM, Subgroup.centralizer_le hQM hzC⟩
  have hzS : z ∈ S := isSylowTwoOf_pCoreOf_le h.sylow_M hzQ
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) := Subgroup.centralizer_le hSM hzC
  have hzZ : z ∈ quasithinOmegaOneCenter S := Subgroup.subset_closure ⟨⟨hzS, hzCS⟩, hz2⟩
  have hcommH : ∀ k ∈ H, k * z = z * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (h.le_centralizer_zb hk) z hzZ).symm
  have hcommM : ∀ m ∈ M, m * z = z * m := fun m hm => Subgroup.mem_centralizer_iff.mp hzC m hm
  have hpow : Subgroup.zpowers z ≤ pCoreOf 2 (M ⊔ H) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · rw [Subgroup.zpowers_le]; exact (le_sup_left : M ≤ M ⊔ H) hzM
    · exact sup_le (fun m hm => mem_normalizer_zpowers_of_comm (hcommM m hm))
        (fun k hk => mem_normalizer_zpowers_of_comm (hcommH k hk))
    · have hod : orderOf z ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hz2
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, hk]
  rw [hA.o2_trivial] at hpow
  have := hpow (Subgroup.mem_zpowers z)
  simpa [Subgroup.mem_bot] using this

theorem V_le_center (h : B2Base H M S) : VZ S M ≤ centerOf (pCoreOf 2 M) :=
  (conjClosure_le_centerOf_pCoreOf_of_sylowIn h.sylow_M.1 h.sylow_M.2.1
    (F7.isSylowTwoOf_odd_relIndex h.sylow_M) (swap h.amalgam).charTwo (le_refl _)).1

theorem isElemAbelian_V (h : B2Base H M S) : IsElemAbelian 2 (VZ S M) :=
  (conjClosure_le_centerOf_pCoreOf_of_sylowIn h.sylow_M.1 h.sylow_M.2.1
    (F7.isSylowTwoOf_odd_relIndex h.sylow_M) (swap h.amalgam).charTwo (le_refl _)).2

theorem V_le_M (h : B2Base H M S) : VZ S M ≤ M :=
  (V_le_center h).trans (inf_le_left.trans ((pCoreOf_le 2 M)))

theorem inf_centralizer_M (h : B2Base H M S) :
    VZ S M ⊓ Subgroup.centralizer (M : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvC⟩
  have hv2 : v ^ 2 = 1 := F7.isElemAbelian_pow_eq_one h.isElemAbelian_V hvV
  have : v ∈ quasithinOmegaOneCenter M :=
    Subgroup.subset_closure ⟨⟨h.V_le_M hvV, hvC⟩, hv2⟩
  rw [h.omegaOneCenter_M] at this
  exact this

theorem inf_centralizer_S (h : B2Base H M S) :
    VZ S M ⊓ Subgroup.centralizer (S : Set G) = quasithinOmegaOneCenter S := by
  apply le_antisymm
  · rintro v ⟨hvV, hvC⟩
    have hvQ : v ∈ pCoreOf 2 M := (h.V_le_center hvV).1
    have hvS : v ∈ S := isSylowTwoOf_pCoreOf_le h.sylow_M hvQ
    have hv2 : v ^ 2 = 1 := F7.isElemAbelian_pow_eq_one h.isElemAbelian_V hvV
    exact Subgroup.subset_closure ⟨⟨hvS, hvC⟩, hv2⟩
  · intro z hz
    exact ⟨le_conjClosure _ _ hz, ((zb_le_S S) hz).2⟩

theorem amalgamHypV (h : B2Base H M S) : AmalgamHypV (M ⊔ H) M H S (VZ S M) := by
  have hA := swap h.amalgam
  have hSP : IsSylowTwoOf S M := h.sylow_M
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M := hA.charTwo
  have hZS : quasithinOmegaOneCenter S ≤ quasithinOmegaOneCenter S := le_rfl
  have hZcent : S ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) := zb_le_centralizer S
  have hO2L : pCoreOf 2 M ≤ S := isSylowTwoOf_pCoreOf_le hSP
  have hZO : pCoreOf 2 M ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) :=
    hO2L.trans hZcent
  have hSZ : S ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G) :=
    hZcent.trans (Subgroup.centralizer_le_normalizer _)
  have hred : IsTwoReducedIn M (conjClosure (quasithinOmegaOneCenter S) M) :=
    isTwoReducedIn_conjClosure_of_sylowIn hSP.1 hSP.2.1 (F7.isSylowTwoOf_odd_relIndex hSP) hF hZS
  have hPN : M ≤ Subgroup.normalizer
      ((conjClosure (quasithinOmegaOneCenter S) M : Subgroup G) : Set G) := hred.2.1
  have hCV : M ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter S) M : Set G) ≤
      pCoreOf 2 M :=
    F112W.centralizer_conjClosure_le_pCoreOf h.amalgam.quot_right hSP hSZ hZO h.not_le_normalizer_zb
  have hCN : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter S) M : Set G) ⊓ M) :=
    (pCoreOf_isPGroup 2 M).to_le (fun x hx => hCV ⟨hx.2, hx.1.2⟩)
  have hCnorm : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter S) M : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hPN.trans (normalizer_le_normalizer_centralizer _))
  have hX : M ≤ Subgroup.normalizer ((S ⊔ M : Subgroup G) : Set G) := by
    rw [sup_eq_right.mpr hSP.1]
    exact Subgroup.le_normalizer
  have hT := F112W.inf_eq_pCoreOf_of_quotient hSP inf_le_left hCnorm Subgroup.le_normalizer hX hCN
  refine { toAmalgamHyp := hA, reduced := hred, cT := ?_ }
  show S ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter S) M : Set G) =
    pCoreOf 2 (M ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter S) M : Set G))
  rw [← hT, ← inf_assoc, inf_eq_left.mpr hSP.1]

theorem inf_centralizer_V (h : B2Base H M S) :
    M ⊓ Subgroup.centralizer (VZ S M : Set G) = pCoreOf 2 M := by
  have hSP : IsSylowTwoOf S M := h.sylow_M
  have hZcent : S ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) := zb_le_centralizer S
  have hZO : pCoreOf 2 M ≤ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) :=
    (isSylowTwoOf_pCoreOf_le hSP).trans hZcent
  have hSZ : S ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G) :=
    hZcent.trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · exact F112W.centralizer_conjClosure_le_pCoreOf h.amalgam.quot_right hSP hSZ hZO
      h.not_le_normalizer_zb
  · intro q hq
    refine ⟨pCoreOf_le 2 M hq, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (h.V_le_center hv).2 q hq).symm

theorem V_ne_bot (h : B2Base H M S) : VZ S M ≠ ⊥ := by
  intro hV
  apply h.zb_ne_bot
  exact le_bot_iff.mp (hV ▸ le_conjClosure (quasithinOmegaOneCenter S) M)

end B2Base

end Amalg

end SzF53B2

end CFSG.Quasithin
