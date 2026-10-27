module

public import CFSG.Quasithin.H13.A6S1516
public import CFSG.Quasithin.H13.A5Sit15g
public import CFSG.Quasithin.H13.A6S1515c

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A5.Orth

@[expose] def TransAt2 (c : OC) (w w' : V4) : Prop :=
  w ≠ 0 → w' ≠ 0 → q w = 0 → q w' = 0 →
    ∃ b : OC, comp b.cols c.cols = comp c.cols b.cols ∧ app b.cols w = w'

instance (c : OC) (w w' : V4) : Decidable (TransAt2 c w w') := by
  unfold TransAt2; infer_instance

@[expose] def TransAt (c : OC) : Prop := Ord3 c.cols → ∀ w w' : V4, TransAt2 c w w'

instance (c : OC) : Decidable (TransAt c) := by unfold TransAt; infer_instance

theorem transAt_all : ∀ c : OC, TransAt c := by
  decide +kernel

theorem exists_comm_of_sing {c : MulAut (Multiplicative V4)} (hc : c ∈ Oq)
    (h3 : c ≠ 1 ∧ c ^ 3 = 1) {w w' : V4} (hw : w ≠ 0) (hw' : w' ≠ 0) (hq : q w = 0)
    (hq' : q w' = 0) : ∃ b ∈ Oq, b * c = c * b ∧
      Multiplicative.toAdd (b (Multiplicative.ofAdd w)) = w' := by
  obtain ⟨b, hbc, hb⟩ := transAt_all (toOC ⟨c, hc⟩)
    (by rw [toOC_mk_cols, ord3_colsOf_iff]; exact h3) w w' hw hw' hq hq'
  obtain ⟨β, rfl⟩ := toOC_surjective b
  rw [toOC_cols, toOC_mk_cols, ← colsOf_mul, ← colsOf_mul, colsOf_eq_iff] at hbc
  rw [toOC_cols, ← app_colsOf] at hb
  exact ⟨β, β.2, hbc, hb⟩

end A5.Orth

namespace A6

@[expose] def A6TL : List (Perm (Fin 6)) :=
  [swap 3 4 * swap 3 5, swap 2 3 * swap 3 5, swap 2 4 * swap 3 5, swap 1 2 * swap 2 5,
    swap 1 4 * swap 3 5, swap 1 4 * swap 2 5, swap 0 1 * swap 1 4, swap 0 1 * swap 1 5,
    swap 0 4 * swap 3 5, swap 0 4 * swap 2 5, swap 1 2 * swap 2 4, swap 0 4 * swap 1 5,
    swap 2 3 * swap 3 4, swap 3 4 * swap 4 5, 1]

theorem A6TL_sign : ∀ σ ∈ A6TL, Perm.sign σ = 1 := by
  decide +kernel

theorem A6TL_trans : ∀ w : P6, InW4 w → w ≠ 1 → ∃ σ ∈ A6TL, act4f σ e0123 = w := by
  decide +kernel

@[expose] def InvTauL : List (Perm (Fin 6)) :=
  [swap 0 4 * swap 1 5, swap 0 2 * swap 1 4 * swap 2 3 * swap 3 5,
    swap 0 2 * swap 1 5 * swap 2 3 * swap 3 4, swap 0 1 * swap 1 2 * swap 2 4 * swap 3 5,
    swap 0 2 * swap 2 4, swap 0 2 * swap 2 5, swap 0 1 * swap 1 3 * swap 2 4 * swap 3 5,
    swap 0 3 * swap 3 4, swap 0 3 * swap 3 5, swap 0 4 * swap 2 5, swap 0 1 * swap 1 4,
    swap 0 4 * swap 3 5, swap 0 5 * swap 2 4, swap 0 1 * swap 1 5, swap 0 5 * swap 3 4,
    swap 2 4 * swap 3 5, swap 2 3 * swap 3 4, swap 2 3 * swap 3 5, 1, swap 3 4 * swap 4 5,
    swap 3 4 * swap 3 5, swap 1 2 * swap 2 3 * swap 2 4 * swap 3 5, swap 1 2 * swap 2 4,
    swap 1 2 * swap 2 5, swap 1 2 * swap 4 5, swap 1 2 * swap 3 4, swap 1 2 * swap 3 5,
    swap 1 2 * swap 1 3 * swap 2 4 * swap 3 5, swap 1 3 * swap 3 4, swap 1 3 * swap 3 5,
    swap 1 2 * swap 1 3, swap 1 3 * swap 2 4, swap 1 3 * swap 2 5, swap 1 4 * swap 2 5,
    swap 1 4 * swap 4 5, swap 1 4 * swap 3 5, swap 1 3 * swap 1 4, swap 1 2 * swap 1 4,
    swap 1 2 * swap 1 3 * swap 1 4 * swap 3 5, swap 1 5 * swap 2 4, swap 1 4 * swap 1 5,
    swap 1 5 * swap 3 4, swap 1 3 * swap 1 5, swap 1 2 * swap 1 5,
    swap 1 2 * swap 1 3 * swap 1 5 * swap 3 4]

theorem InvTauL_sign : ∀ τ ∈ InvTauL, Perm.sign τ = 1 := by
  decide +kernel

@[expose] def InvConjAt (σ : Perm (Fin 6)) : Prop :=
  Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 → ∃ τ ∈ InvTauL, τ⁻¹ * σ * τ = swap 0 1 * swap 2 3

instance (σ : Perm (Fin 6)) : Decidable (InvConjAt σ) := by unfold InvConjAt; infer_instance

theorem invConjAt_all : ∀ σ : Perm (Fin 6), InvConjAt σ := by
  decide +kernel

theorem s0123_W3 : ∀ w : P6, InW4 w →
    (act4f (swap 0 1 * swap 2 3)⁻¹ w * w = 1 ∨ act4f (swap 0 1 * swap 2 3)⁻¹ w * w = e0123) →
      InW3 w := by
  decide +kernel

theorem s0123_K4L : swap 0 1 * swap 2 3 ∈ K4L := by
  decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_conj_z_of_V {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ g : G, g * S.z * g⁻¹ = v := by
  have hw : ((S.frame.ψ ⟨v, hv⟩ : ↥W4) : P6) ≠ 1 := by
    intro h
    apply hv1
    have h1 : S.frame.ψ ⟨v, hv⟩ = 1 := Subtype.ext h
    rw [← map_one S.frame.ψ] at h1
    exact congrArg Subtype.val (S.frame.ψ.injective h1)
  obtain ⟨σ, hσL, hσ⟩ := A6TL_trans _ (S.frame.ψ ⟨v, hv⟩).2 hw
  obtain ⟨l, -, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 (A6TL_sign σ hσL))
  refine ⟨l, ?_⟩
  have hzv : (l : G) * S.z * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 _).mp S.z_mem_V
  have h := S.psi_conj_coe l S.z_mem_V hzv
  rw [hl, S.psi_z] at h
  have h2 : S.frame.ψ ⟨_, hzv⟩ = S.frame.ψ ⟨v, hv⟩ := Subtype.ext (h.trans hσ)
  exact congrArg Subtype.val (S.frame.ψ.injective h2)

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hna

theorem exists_conj_z_of_UH
    {SY : A5SitY (S.toA5Sit hNS h13315 h1356two hH hna) S.L1}
    (P : A5SitPf15 (S.toA5Sit hNS h13315 h1356two hH hna) SY) {u : G}
    (hu : u ∈ conjClosure S.V3 H) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g : G, g * S.z * g⁻¹ = u := by
  have hz := S.C_z_eq hNS h13315 h1356two hH hna P
  set A := S.toA5Sit hNS h13315 h1356two hH hna
  by_cases huV : u = P.C.z
  · exact ⟨1, by rw [huV, hz]; group⟩
  have hθu : P.C.θ ⟨u, hu⟩ ≠ 1 := by
    intro h
    rcases (P.C.ker_iff _).1 h with h | h
    · exact hu1 h
    · exact huV h
  have hsq : ∀ (x : ↥(conjClosure S.V3 H)), (x : G) * x = 1 →
      q (Multiplicative.toAdd (P.C.θ x)) = 0 := by
    intro x hx
    rcases P.C.sq x with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      apply P.C.z_ne
      rw [← h, pow_two, hx]
  have hne0 : ∀ (x : ↥(conjClosure S.V3 H)), P.C.θ x ≠ 1 →
      Multiplicative.toAdd (P.C.θ x) ≠ 0 := fun x hx h => hx (by
        rw [← toAdd_one] at h
        exact Multiplicative.toAdd.injective h)
  obtain ⟨u₃, hu₃, hu₃'⟩ : ∃ u₃ ∈ S.V3, u₃ ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show S.V3 ≤ fsuV1 T V from h)
    rw [S.card_V3, S.card_V1] at this
    omega
  have hu₃U : u₃ ∈ conjClosure S.V3 H := le_conjClosure _ _ hu₃
  have hu₃V : u₃ ∈ V := S.V3_le_V hu₃
  have hu₃2 : u₃ * u₃ = 1 := by
    rw [← pow_two]
    exact S.elemAbelian_V.2 u₃ hu₃V
  have hθu₃ : P.C.θ ⟨u₃, hu₃U⟩ ≠ 1 := by
    intro h
    exact hu₃' ((P.Cz u₃).2 ((P.C.ker_iff _).1 h))
  obtain ⟨b, hbO, hbc, hb⟩ := exists_comm_of_sing P.ch_props.1
    ⟨P.ch_props.2.1, P.ch_props.2.2⟩ (hne0 _ hθu₃) (hne0 _ hθu)
    (hsq _ hu₃2) (hsq _ hu2)
  obtain ⟨x, -, hx⟩ := P.centralizer_le_Φ hbO hbc
  have hxu : (x : G) * u₃ * (x : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ x.2) u₃).mp hu₃U
  have hθ : P.C.θ ⟨(x : G) * u₃ * (x : G)⁻¹, hxu⟩ = P.C.θ ⟨u, hu⟩ := by
    have h1 : P.Φ x (P.C.θ ⟨u₃, hu₃U⟩) = P.C.θ ⟨(x : G) * u₃ * (x : G)⁻¹, hxu⟩ := by
      unfold A5SitPf15.Φ
      rw [Q8Coords.act_θ]
      rfl
    rw [← h1, hx]
    apply Multiplicative.toAdd.injective
    rw [← hb, ofAdd_toAdd]
  obtain ⟨g₃, hg₃⟩ := S.exists_conj_z_of_V hu₃V (fun h => hu₃' (h ▸ (fsuV1 T V).one_mem))
  set u' := (x : G) * u₃ * (x : G)⁻¹ with hu'
  have hk : P.C.θ (⟨u, hu⟩ * (⟨u', hxu⟩ : ↥(conjClosure S.V3 H))⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ]
    exact mul_inv_cancel _
  rcases (P.C.ker_iff _).1 hk with h | h
  ·
    have e : u = u' := by
      have h' : u * u'⁻¹ = 1 := h
      exact mul_inv_eq_one.1 h'
    refine ⟨(x : G) * g₃, ?_⟩
    rw [e, hu', ← hg₃]
    group
  ·
    have e : u = P.C.z * u' := by
      have h' : u * u'⁻¹ = P.C.z := h
      rw [← h']
      group
    have hθu' : Multiplicative.toAdd (P.C.θ ⟨u', hxu⟩) ≠ 0 := by
      rw [hθ]
      exact hne0 _ hθu
    obtain ⟨y, hy⟩ : ∃ y : V4, Bf (Multiplicative.toAdd (P.C.θ ⟨u', hxu⟩)) y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hθu' (Bf_nondeg _ hcon)
    obtain ⟨w', hw'⟩ := P.C.θ_surj (Multiplicative.ofAdd y)
    have hnc : ¬ (((⟨u', hxu⟩ : ↥(conjClosure S.V3 H)) : G) * (w' : G) =
        w' * ((⟨u', hxu⟩ : ↥(conjClosure S.V3 H)) : G)) := by
      rw [P.comm_iff_Bf ⟨u', hxu⟩ w', hw', toAdd_ofAdd]
      exact hy
    have hcm : P.C.θ (w' * ⟨u', hxu⟩ * w'⁻¹ * (⟨u', hxu⟩ : ↥(conjClosure S.V3 H))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_one]
      abel
    rcases (P.C.ker_iff _).1 hcm with h2 | h2
    · exfalso
      apply hnc
      have h2' : (w' : G) * u' * (w' : G)⁻¹ * u'⁻¹ = 1 := h2
      have : (w' : G) * u' = u' * w' := by
        calc (w' : G) * u' = (w' : G) * u' * (w' : G)⁻¹ * u'⁻¹ * (u' * w') := by group
          _ = u' * w' := by rw [h2', one_mul]
      exact this.symm
    · have h2' : (w' : G) * u' * (w' : G)⁻¹ * u'⁻¹ = P.C.z := h2
      refine ⟨(w' : G) * x * g₃, ?_⟩
      have e2 : (w' : G) * u' * (w' : G)⁻¹ = P.C.z * u' := by rw [← h2']; group
      rw [e, ← e2, hu', ← hg₃]
      group

variable (hhat : ¬ IsHatA6 L) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six) (hctk : Input13515CTK)
include hhat hn hlL hl hobl hctk

theorem mem_V_of_rho
    {t : ↥(Subgroup.normalizer (V : Set G))} (htL : (t : G) ∈ L)
    (h1 : S.frame.ρ t = 1) : (t : G) ∈ V := by
  have hOM := S.pCoreOf_M_eq_V hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
  have htC := (S.rho_eq_one_iff t).1 h1
  have htM : (t : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer htL
  have htC' : (t : G) ∈ Subgroup.centralizer
      (pCoreOf 2 (Subgroup.normalizer (L : Set G)) : Set G) := by
    rw [hOM]
    exact htC
  have h := S.charTwo_M ⟨htM, htC'⟩
  rwa [hOM] at h

theorem exists_conj_z_of_L
    {t : G} (htL : t ∈ L) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : G, g * S.z * g⁻¹ = t := by
  have htN : t ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le htL
  by_cases hρ : S.frame.ρ ⟨t, htN⟩ = 1
  · exact S.exists_conj_z_of_V
      (S.mem_V_of_rho hNS h13315 h1356two hH hna hhat hn hlL hl hobl hctk htL hρ) ht1
  have hσs : Perm.sign (S.frame.ρ ⟨t, htN⟩) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨⟨t, htN⟩, htL, rfl⟩)
  have hσ2 : S.frame.ρ ⟨t, htN⟩ * S.frame.ρ ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htN⟩ : ↥(Subgroup.normalizer (V : Set G))) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨τ, hτL, hτ⟩ := invConjAt_all _ hσs hσ2 hρ
  obtain ⟨k, hkL, hk⟩ := (S.frame.image_L τ).2 (Perm.mem_alternatingGroup.2 (InvTauL_sign τ hτL))
  set t' : ↥(Subgroup.normalizer (V : Set G)) := k⁻¹ * ⟨t, htN⟩ * k with ht'
  have ht'ρ : S.frame.ρ t' = swap 0 1 * swap 2 3 := by
    rw [ht', map_mul, map_mul, map_inv, hk, hτ]
  have ht'L : (t' : G) ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem hkL) htL) hkL
  have ht'2 : (t' : G) * t' = 1 := by
    rw [ht']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (k : G)⁻¹ * t * k * ((k : G)⁻¹ * t * k) = (k : G)⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [ht2]; group
  have hte : t = (k : G) * t' * (k : G)⁻¹ := by
    rw [ht']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have ht'1 : (t' : G) ≠ 1 := by
    intro h
    apply ht1
    rw [hte, h]
    group
  have hUL1 := S.UH_le_L1_six hNS h13315 h1356two hH hn hna
  obtain ⟨-, hsurj⟩ := S.lemma13_5_14_two hNS h1356two h13315 hH hUL1 hna
  obtain ⟨u₀, hu₀, hρu₀⟩ := hsurj _ s0123_K4L
  have hu₀N : u₀ ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu₀))
  have hvρ : S.frame.ρ ((⟨u₀, hu₀N⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * t') = 1 := by
    rw [map_mul, map_inv, hρu₀, ht'ρ, inv_mul_cancel]
  have hvL : (((⟨u₀, hu₀N⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * t' :
      ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L :=
    L.mul_mem (L.inv_mem (S.L1_le_L (hUL1 hu₀))) ht'L
  have hvV := S.mem_V_of_rho hNS h13315 h1356two hH hna hhat hn hlL hl hobl hctk hvL hvρ
  set v : G := (((⟨u₀, hu₀N⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * t' :
      ↥(Subgroup.normalizer (V : Set G))) : G) with hv
  have hvdef : v = u₀⁻¹ * t' := rfl
  have ht'v : (t' : G) = u₀ * v := by
    rw [hvdef]
    group
  obtain ⟨P⟩ := S.nonempty_pf15_six hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  have hu₀sq : u₀ * u₀ = 1 ∨ u₀ * u₀ = P.C.z := by
    rcases P.C.sq ⟨u₀, hu₀⟩ with ⟨-, h⟩ | ⟨-, h⟩
    · left
      rw [← pow_two]
      exact h
    · right
      rw [← pow_two]
      exact h
  have hconj : u₀⁻¹ * v * u₀ ∈ V := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu₀N) v).mp hvV
    simpa using h
  have hprod : u₀⁻¹ * v * u₀ * v = (u₀ * u₀)⁻¹ := by
    rw [ht'v] at ht'2
    calc u₀⁻¹ * v * u₀ * v = (u₀ * u₀)⁻¹ * (u₀ * v * (u₀ * v)) := by group
      _ = (u₀ * u₀)⁻¹ := by rw [ht'2, mul_one]
  have hψ := S.psi_conj_inv_coe ⟨u₀, hu₀N⟩ hvV hconj
  rw [hρu₀] at hψ
  have hψprod : ((S.frame.ψ ⟨u₀⁻¹ * v * u₀ * v, V.mul_mem hconj hvV⟩ : ↥W4) : P6) =
      act4f (swap 0 1 * swap 2 3)⁻¹ (S.frame.ψ ⟨v, hvV⟩) * (S.frame.ψ ⟨v, hvV⟩ : P6) := by
    have e : (⟨u₀⁻¹ * v * u₀ * v, V.mul_mem hconj hvV⟩ : ↥V) =
        ⟨u₀⁻¹ * v * u₀, hconj⟩ * ⟨v, hvV⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul, hψ]
  have hzz : P.C.z = S.z := S.C_z_eq hNS h13315 h1356two hH hna P
  have hvW3 : InW3 (S.frame.ψ ⟨v, hvV⟩ : P6) := by
    refine s0123_W3 _ (S.frame.ψ ⟨v, hvV⟩).2 ?_
    rw [← hψprod]
    rcases hu₀sq with h | h
    · left
      have e : (⟨u₀⁻¹ * v * u₀ * v, V.mul_mem hconj hvV⟩ : ↥V) = 1 :=
        Subtype.ext (by
          show u₀⁻¹ * v * u₀ * v = 1
          rw [hprod, h, inv_one])
      rw [e, map_one, OneMemClass.coe_one]
    · right
      have e : (⟨u₀⁻¹ * v * u₀ * v, V.mul_mem hconj hvV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
        Subtype.ext (by
          show u₀⁻¹ * v * u₀ * v = S.z
          rw [hprod, h, hzz]
          exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact S.z_sq))
      rw [e, S.psi_z]
  have hvV3 : v ∈ S.V3 := S.mem_pre.2 ⟨hvV, hvW3⟩
  have ht'U : (t' : G) ∈ conjClosure S.V3 H := by
    rw [ht'v]
    exact (conjClosure S.V3 H).mul_mem hu₀ (le_conjClosure _ _ hvV3)
  obtain ⟨g, hg⟩ := S.exists_conj_z_of_UH hNS h13315 h1356two hH hna P ht'U ht'2 ht'1
  refine ⟨(k : G) * g, ?_⟩
  rw [hte, ← hg]
  group

end Data

end Setting4

end A6

end CFSG.Quasithin.H13
