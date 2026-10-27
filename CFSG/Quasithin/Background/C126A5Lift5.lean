module

public import CFSG.Quasithin.Background.C126A5Lift4
public import CFSG.Quasithin.Background.C126A5Lift3

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_pow_three {c : G} (h3 : c ^ 3 = 1) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have := Nat.dvd_gcd h1 h2
  rw [hg] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem coversAlt : CoversAlt d.θ (autI hV (Khat s d x)) := by
  intro g hg
  have hg' : g ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]; exact mem_alts.1 hg
  rw [← normalClosure_cyc3 d.π] at hg'
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  let F := autI hV (Khat s d x)
  let Sg : Subgroup (Perm (Fin 5)) := ((F ⊓ d.L).subgroupOf d.L).map d.θ.toMonoidHom
  have hconj : ∀ u : Perm (Fin 5), u * cyc3 d.π * u⁻¹ ∈ Sg := by
    intro u
    obtain ⟨φ, hφ, hφu⟩ := d.exists_of_th (g := u)
    obtain ⟨a, ha, hav⟩ := exists_A₁_cv (s := s) (d := d) hφ
    have haH : a ∈ H := (mem_A₁.1 ha).1
    have hk : a * x * a⁻¹ ∈ Khat s d x :=
      mem_conjClosure ha (Subgroup.mem_zpowers x)
    have hkcv : cv hV (a * x * a⁻¹) = φ * cv hV x * φ⁻¹ := by
      rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N haH) (s.H_le_N (s.Y_le hx.mem)))
        (s.H_le_N (H.inv_mem haH)), cv_mul hV (s.H_le_N haH) (s.H_le_N (s.Y_le hx.mem)),
        cv_inv hV (s.H_le_N haH), hav]
    have hkL : cv hV (a * x * a⁻¹) ∈ d.L := by
      rw [hkcv]; exact d.L.mul_mem (d.L.mul_mem hφ hx.mem_L) (d.L.inv_mem hφ)
    have hkF : cv hV (a * x * a⁻¹) ∈ F := (mem_autI_iff hV hKN).2 ⟨_, hk, rfl⟩
    refine ⟨⟨cv hV (a * x * a⁻¹), hkL⟩, Subgroup.mem_subgroupOf.2 ⟨hkF, hkL⟩, ?_⟩
    show d.θ ⟨cv hV (a * x * a⁻¹), hkL⟩ = _
    rw [← d.th_of_mem hkL, hkcv, d.th_mul (d.L.mul_mem hφ hx.mem_L) (d.L.inv_mem hφ),
      d.th_mul hφ hx.mem_L, d.th_inv hφ, hφu, hx.th_eq]
  have hle : Subgroup.normalClosure {cyc3 d.π} ≤ Sg := by
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨b, hb, hyb⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨u, hu⟩ := isConj_iff.1 hyb
    rw [← hu]
    exact hconj u
  obtain ⟨h, hh, hθ⟩ := hle hg'
  exact ⟨h, (Subgroup.mem_subgroupOf.1 hh).1, hθ⟩

theorem irred_Vc {W₀ : Subgroup G} (hW : W₀ ≤ Vc d)
    (hN : Khat s d x ≤ Subgroup.normalizer (W₀ : Set G)) : W₀ = ⊥ ∨ W₀ = Vc d := by
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  set U' : Subgroup (IntMod V hV) := W₀.comap (valHom hV) with hU'
  have hU'le : U' ≤ commV d.L := by
    intro w hw
    obtain ⟨w', hw', hww⟩ := mem_Vc.1 (hW hw)
    have : w' = w := IntMod.val_injective hww
    exact this ▸ hw'
  have hinv : ∀ h ∈ autI hV (Khat s d x), ∀ u ∈ U', h u ∈ U' := by
    intro h hh u hu
    obtain ⟨k, hk, rfl⟩ := (mem_autI_iff hV hKN).1 hh
    show valHom hV (cv hV k u) ∈ W₀
    show (cv hV k u).val ∈ W₀
    rw [cv_val hV (hKN hk)]
    exact (Subgroup.mem_normalizer_iff.1 (hN hk) u.val).1 hu
  rcases irred_commV d.θ d.β d.hβ hx.coversAlt hU'le hinv with hbot | htop
  · left
    refine le_antisymm (fun u hu => ?_) bot_le
    obtain ⟨w, hw, rfl⟩ := mem_Vc.1 (hW hu)
    have : w ∈ U' := hu
    rw [hbot, Subgroup.mem_bot] at this
    rw [this]; exact (Subgroup.mem_bot.2 rfl)
  · right
    refine le_antisymm hW (fun u hu => ?_)
    obtain ⟨w, hw, rfl⟩ := mem_Vc.1 hu
    have : w ∈ U' := htop ▸ hw
    exact this

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem blockU_le_Vc : blockU (Khat s d x) ≤ Vc d := by
  unfold blockU blockQ
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haQ : a ∈ pCoreOf 2 H := (hx.pCoreOf_Khat ▸ ha).2
  have := (mem_cqK.1 (hx.Khat_le_cq hY hA3 hb)).2 a haQ
  have e : ⁅a, b⁆ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (Vc d).inv_mem this

theorem blockU_ne_bot : blockU (Khat s d x) ≠ ⊥ := by
  intro hbot
  obtain ⟨c, ⟨v, hv, hcv⟩, hc1⟩ : ∃ c ∈ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹}, c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹} ⊆ {1} := fun c hc => hcon c hc
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := hx.four_comm_V
    rw [Set.ncard_singleton] at h1
    omega
  have hvQ : v ∈ pCoreOf 2 H := MinParabolic.le_pCoreOf_of_isTwoReduced s.red hv
  have hvA : v ∈ A₁ s d := Q_le_A₁ hvQ
  have hxK : x ∈ Khat s d x := hx.zpowers_le_Khat (Subgroup.mem_zpowers x)
  have hcK : c ∈ Khat s d x := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hx.A₁_le_normalizer_Khat hvA) x⁻¹).1
      ((Khat s d x).inv_mem hxK)
    have := (Khat s d x).mul_mem hxK h1
    rw [hcv]
    simpa [mul_assoc] using this
  have hxH : x ∈ H := s.Y_le hx.mem
  have hcQ : c ∈ pCoreOf 2 H := by
    have h1 : x * v * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hxH) v).1 hvQ
    rw [hcv]
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hvQ)
  have hcO : c ∈ blockQ (Khat s d x) := by
    show _ ∈ pCoreOf 2 (Khat s d x)
    rw [hx.pCoreOf_Khat]; exact ⟨hcK, hcQ⟩
  have hU : c * x * c⁻¹ * x⁻¹ ∈ blockU (Khat s d x) := C1.commutator_mem_blockU hcO hxK
  rw [hbot, Subgroup.mem_bot] at hU
  have h2 : c * x * c⁻¹ = x := mul_inv_eq_one.1 hU
  have h3 : c * x = x * c := by
    have := congrArg (· * c) h2
    simpa [mul_assoc] using this
  have hcomm : x * c * x⁻¹ = c := by
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [h3]
      _ = c := by group
  have hnorm := norm_comm_eq_one (x := x) (q := v) (by rw [← hx.ord]; exact pow_orderOf_eq_one x)
  rw [← hcv] at hnorm
  simp only [hcomm] at hnorm
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨c, hcQ⟩
  exact hc1 (eq_one_of_pow_three (by simpa [pow_succ, mul_assoc] using hnorm)
    (congrArg Subtype.val hk))

theorem blockU_eq_Vc : blockU (Khat s d x) = Vc d := by
  have hle := hx.blockU_le_Vc hY hA3
  rcases hx.irred_Vc hle (C1.le_normalizer_blockU _) with h | h
  · exact absurd h (hx.blockU_ne_bot hY hA3)
  · exact h

theorem blockZ_eq_bot : blockZ (Khat s d x) = ⊥ := by
  refine le_antisymm (fun u hu => ?_) bot_le
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  have huV : u ∈ Vc d := hx.blockU_eq_Vc hY hA3 ▸ hu.1
  obtain ⟨w, hw, rfl⟩ := mem_Vc.1 huV
  have hfix : ∀ h ∈ autI hV (Khat s d x), h w = w := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := (mem_autI_iff hV hKN).1 hh
    apply IntMod.val_injective
    rw [cv_val hV (hKN hk), Subgroup.mem_centralizer_iff.1 hu.2 k hk]
    group
  have h1 := fix_commV d.θ d.β d.hβ hx.coversAlt hw hfix
  rw [h1]
  exact Subgroup.one_mem _

end XData

end Lift

end CFSG.Quasithin.C126.A5
