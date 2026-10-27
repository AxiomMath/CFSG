module

public import CFSG.Quasithin.H13.L32A770b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem comm_le_inf (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ≤
      fsuU T V ⊓ conjSub ((k : G) * g) (fsuU T V) := by
  rw [← uα_eq (g := g) (k := k) h hMod, fsuU_eq_conjClosure_hz hMod h]
  exact N.commutator_le hF

theorem comm_mem_of_card_four (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h4 : Nat.card ↥(u0 T V) = 4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (hZ : conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ ⊔ u0 T V)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {s : G} (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hsQ : s ∉ pCoreOf 2 (hz T V))
    (hW : ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
      w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V)) :
    ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V) := by
  have h13322 := stmt13_3_2_two_of h1332
  have hV1U0 := fsuV1_le_u0 h hMod
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hTH : T ≤ hz T V := hF.T_le_H
  have hsH : s ∈ hz T V := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact ((pCoreOf_le_of_le h le_sup_right).trans hTH) (this hsW)
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  have hZU0 := N.zα_not_le_u0 hF h68 h
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hF.card_V₁
  set x : G := (k : G) * g with hx
  set z' : G := x * z * x⁻¹ with hz'
  have hz'Z : z' ∈ conjSub x (fsuV1 T V) := mul_mem_conjSub hzV1
  have hZgen : ∀ y ∈ conjSub x (fsuV1 T V), y = 1 ∨ y = z' := by
    intro y hy
    rw [mem_conjSub] at hy
    rcases hgen _ hy with e | e
    · left
      rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, e]
      group
    · right
      rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, e]
  have hz'U : z' ∈ fsuU T V := (Subgroup.mem_inf.mp (N.comm_le_inf h hMod hF (hZF hz'Z))).1
  have hz'U0 : z' ∉ u0 T V := by
    intro hm
    apply hZU0
    intro y hy
    rcases hZgen y hy with rfl | rfl
    · exact one_mem _
    · exact hm
  have hidx2 := relIndex_eq_two_of_card hV2.1 hF.card_V₁ hV2.2.2.2
  have hidx0 := relIndex_eq_two_of_card hV1U0 hF.card_V₁ h4
  have hT : ∀ t ∈ T, t * z' * t⁻¹ * z'⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have htH := hTH ht
    have hV2N : V₂ ≤ Subgroup.normalizer (u0 T V : Set G) :=
      (hV2.2.1.trans (hVU.trans hUH)).trans (hz_le_normalizer_u0 h hMod)
    have hz'' := hZ hz'Z
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV2N] at hz''
    obtain ⟨a, ha, u, hu, hau⟩ := hz''
    have h1 := comm_mem_of_relIndex_two hidx2 (hV2.2.2.1 ht) (hF.H_normalizes_V₁ htH) ha
    have h2 := comm_mem_of_relIndex_two hidx0 (hz_le_normalizer_u0 h hMod htH)
      (hF.H_normalizes_V₁ htH) hu
    have h3 : a * (t * u * t⁻¹ * u⁻¹) * a⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ (hUH (hVU (hV2.2.1 ha)))) _).mp h2
    rw [← hau, show t * (a * u) * t⁻¹ * (a * u)⁻¹ = (t * a * t⁻¹ * a⁻¹) *
      (a * (t * u * t⁻¹ * u⁻¹) * a⁻¹) by group]
    exact mul_mem h1 h3
  obtain ⟨q, hq, hqz⟩ : ∃ q ∈ pCoreOf 2 (hz T V), q * z' ≠ z' * q := by
    by_contra hc
    push Not at hc
    exact hz'U0 (mem_u0_of_comm h hMod h63 hF h1222 h13322 h13314 h4 hz'U hc)
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  have hqz' : q * z' * q⁻¹ * z'⁻¹ = z := by
    rcases hgen _ (comm_mem_of_pCoreOf h hMod hF hq hz'U) with e | e
    · exact absurd (by
        calc q * z' = q * z' * q⁻¹ * z'⁻¹ * (z' * q) := by group
          _ = z' * q := by rw [e, one_mul]) hqz
    · exact e
  have hzc : ∀ y ∈ hz T V, z * y = y * z := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hy z hzV1
  have hzconj : ∀ y ∈ hz T V, y⁻¹ * z * y = z := fun y hy => by
    rw [mul_assoc, hzc y hy, ← mul_assoc, inv_mul_cancel, one_mul]
  have hz2 : z * z = 1 := by
    have h1 := orderOf_dvd_natCard (⟨z, hzV1⟩ : ↥(fsuV1 T V))
    rw [hF.card_V₁] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : z ^ 2 = 1 := by simpa using congrArg Subtype.val h2
    rwa [pow_two] at h3
  intro t ht
  have htH := hTH ht
  obtain ⟨t', ht'H, ht'z, q', hq', rfl⟩ : ∃ t' ∈ hz T V, t' * z' * t'⁻¹ = z' ∧
      ∃ q' ∈ pCoreOf 2 (hz T V), t = q' * t' := by
    rcases hgen _ (hT t ht) with e | e
    · refine ⟨t, htH, ?_, 1, one_mem _, by group⟩
      calc t * z' * t⁻¹ = t * z' * t⁻¹ * z'⁻¹ * z' := by group
        _ = z' := by rw [e, one_mul]
    · refine ⟨q⁻¹ * t, mul_mem (inv_mem hqH) htH, ?_, q, hq, by group⟩
      have e1 : t * z' * t⁻¹ = z * z' := by
        calc t * z' * t⁻¹ = t * z' * t⁻¹ * z'⁻¹ * z' := by group
          _ = z * z' := by rw [e]
      have e2 : q⁻¹ * z' * q = z * z' := by
        have e3 : q * z' * q⁻¹ = z * z' := by
          calc q * z' * q⁻¹ = q * z' * q⁻¹ * z'⁻¹ * z' := by group
            _ = z * z' := by rw [hqz']
        have e4 : z' = z * (q⁻¹ * z' * q) := by
          calc z' = q⁻¹ * (q * z' * q⁻¹) * q := by group
            _ = q⁻¹ * (z * z') * q := by rw [e3]
            _ = (q⁻¹ * z * q) * (q⁻¹ * z' * q) := by group
            _ = z * (q⁻¹ * z' * q) := by rw [hzconj q hqH]
        calc q⁻¹ * z' * q = z * z * (q⁻¹ * z' * q) := by rw [hz2, one_mul]
          _ = z * z' := by rw [mul_assoc, ← e4]
      calc q⁻¹ * t * z' * (q⁻¹ * t)⁻¹ = q⁻¹ * (t * z' * t⁻¹) * q := by group
        _ = q⁻¹ * (z * z') * q := by rw [e1]
        _ = (q⁻¹ * z * q) * (q⁻¹ * z' * q) := by group
        _ = z * (z * z') := by rw [hzconj q hqH, e2]
        _ = z' := by rw [← mul_assoc, hz2, one_mul]
  have ht'α : t' ∈ conjSub x (hz T V) := by
    have h1 : t' ∈ Subgroup.centralizer (conjSub x (fsuV1 T V) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hZgen y hy with rfl | rfl
      · group
      · calc z' * t' = t' * z' * t'⁻¹ * t' := by rw [ht'z]
          _ = t' * z' := by group
    rw [conjSub_centralizer] at h1
    exact h1
  have ht'W : t' * s * t'⁻¹ ∈ conjSub x (fsuU T V) :=
    (Subgroup.mem_normalizer_iff.mp
      (conjSub_le_normalizer (g := x) (hz_le_normalizer_U h hMod) ht'α) s).mp hsW
  have ht'Q : t' * s * t'⁻¹ ∉ pCoreOf 2 (hz T V) := fun hm => hsQ (by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ ht'H) s).mpr hm
    exact this)
  have hd := (hW _ ht'W).resolve_left ht'Q
  have hq'H : q' ∈ hz T V := pCoreOf_le 2 _ hq'
  have e : q' * t' * s * (q' * t')⁻¹ * s⁻¹ =
      s * ((s⁻¹ * q' * s) * (s⁻¹ * (t' * s * t'⁻¹)) * q'⁻¹) * s⁻¹ := by group
  rw [e]
  refine (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hsH) _).mp
    (mul_mem (mul_mem ?_ hd) (inv_mem hq'))
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hsH)) q').mp hq'
  rwa [inv_inv] at this

theorem T_le_normalizer (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {s : G}
    (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hW : ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
      w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V))
    (hTs : ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V)) :
    T ≤ Subgroup.normalizer
      ((⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ fsuV1 T V : Subgroup G) : Set G) := by
  have hTH : T ≤ hz T V := hF.T_le_H
  have hWR : conjSub ((k : G) * g) (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [← uα_eq (g := g) (k := k) h hMod]
    exact N.uα_le hF
  have hWH : conjSub ((k : G) * g) (fsuU T V) ≤ hz T V :=
    hWR.trans ((pCoreOf_le_of_le h le_sup_right).trans hTH)
  have hsH := hWH hsW
  intro t ht
  have htH := hTH ht
  have hWt : conjSub t (conjSub ((k : G) * g) (fsuU T V)) ≤
      conjSub ((k : G) * g) (fsuU T V) ⊔ pCoreOf 2 (hz T V) := by
    intro y hy
    rw [mem_conjSub] at hy
    set w := t⁻¹ * y * t with hw
    have hyw : y = t * w * t⁻¹ := by rw [hw]; group
    rcases hW w hy with hwQ | hwQ
    · refine Subgroup.mem_sup_right ?_
      rw [hyw]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ htH) w).mp hwQ
    · have h1 := hTs t ht
      have h2 : t * (s⁻¹ * w) * t⁻¹ ∈ pCoreOf 2 (hz T V) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ htH) _).mp hwQ
      have h3 : s⁻¹ * (t * s * t⁻¹ * s⁻¹) * s ∈ pCoreOf 2 (hz T V) := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hsH)) _).mp h1
        rwa [inv_inv] at this
      rw [hyw, show t * w * t⁻¹ = s * ((s⁻¹ * (t * s * t⁻¹ * s⁻¹) * s) *
        (t * (s⁻¹ * w) * t⁻¹)) by group]
      exact Subgroup.mul_mem_sup hsW (mul_mem h3 h2)
  have hUt : conjSub t (fsuU T V) = fsuU T V :=
    conjSub_eq_self_iff.mpr (hz_le_normalizer_U h hMod htH)
  have hV1t : conjSub t (fsuV1 T V) = fsuV1 T V := conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ htH)
  rw [← conjSub_eq_self_iff]
  refine conjSub_eq_of_le ?_
  rw [conjSub_sup, ← conjSub_commutator, hUt, hV1t]
  refine sup_le ?_ le_sup_right
  refine (Subgroup.commutator_mono le_rfl hWt).trans (commutator_sup_le ?_ ?_ ?_)
  · exact hWH.trans hF.H_normalizes_V₁
  · exact hWH.trans (le_normalizer_pCoreOf 2 _)
  · exact fun q hq u hu => comm_mem_of_pCoreOf h hMod hF hq hu

theorem zα_le_of_card_four (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h68 : Lemma14_7_68) (h4 : Nat.card ↥(u0 T V) = 4) {V₂ : Subgroup G}
    (hV2 : A6.IsV2 T V V₂) (hZ : conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ ⊔ u0 T V)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ ∧
      ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ V = V ⊔ u0 T V := by
  have h13322 := stmt13_3_2_two_of h1332
  have hV1U0 := fsuV1_le_u0 h hMod
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  have hTH : T ≤ hz T V := hF.T_le_H
  obtain ⟨-, hV8, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  obtain ⟨s, hsW, hsQ, hW⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  set F := ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ with hFdef
  set P := F ⊔ fsuV1 T V with hP
  have hTs := N.comm_mem_of_card_four h hMod h63 hF h1222 h1332 h1334 h13314 h68 h4 hV2 hZ h2
    hsW hsQ hW
  have hTP := N.T_le_normalizer h hMod hF hsW hW hTs
  have hPU0 : P ⊓ u0 T V = fsuV1 T V := N.sup_inf_u0 h hMod hF h64 hsW hsQ hW
  have hFU0 : F ⊔ u0 T V = V ⊔ u0 T V := N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ
  have hFU : F ≤ fsuU T V := (N.comm_le_inf h hMod hF).trans inf_le_left
  have hPU : P ≤ fsuU T V := sup_le hFU (hV1U0.trans hU0U)
  obtain ⟨⟨u₀, hu₀, hcV, hcV1⟩, hR5⟩ := ((h64 G T L V h).2.2.2.2 h4).1 s hsR hsQ
  set c := u₀ * s * u₀⁻¹ * s⁻¹ with hc
  have hcP : c ∈ P := (N.mem_sup_iff h hMod hF hsW hW).mpr ⟨u₀, hu₀, by
    rw [← hc, mul_inv_cancel]
    exact one_mem _⟩
  have hPV : ∀ y ∈ P, y ∈ V → y ∈ fsuV1 T V ∨ y * c⁻¹ ∈ fsuV1 T V := by
    intro y hyP hyV
    obtain ⟨u, hu, hyu⟩ := (N.mem_sup_iff h hMod hF hsW hW).mp hyP
    have huV : u * s * u⁻¹ * s⁻¹ ∈ V := by
      rw [show u * s * u⁻¹ * s⁻¹ = (y * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ * y by group]
      exact mul_mem (inv_mem (hV1V hyu)) hyV
    rcases hR5 u₀ hu₀ u hu hcV huV with h1 | h1 | h1
    · exact absurd h1 hcV1
    · left
      rw [show y = (y * (u * s * u⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹) by group]
      exact mul_mem hyu h1
    · right
      rw [show y * c⁻¹ = (y * (u * s * u⁻¹ * s⁻¹)⁻¹) * (c * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ by group]
      exact mul_mem hyu (inv_mem h1)
  have hcT : ∀ t ∈ T, t * c * t⁻¹ * c⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have h1 : t * c * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hTP ht) c).mp hcP
    have h2 : t * c * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV ht) c).mp hcV
    rcases hPV _ h1 h2 with h3 | h3
    · exact absurd ((Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ (hTH ht)) c).mpr h3)
        hcV1
    · exact h3
  have hc2 : c ^ 2 = 1 := F7.isElemAbelian_pow_eq_one (isElemAbelian_fsuU_of h hMod) (hVU hcV)
  have hc1 : c ≠ 1 := fun e => hcV1 (e ▸ one_mem _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_c : Nat.card ↥(Subgroup.zpowers c) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1]
  have hinf : Subgroup.zpowers c ⊓ fsuV1 T V = ⊥ := by
    by_contra hne
    exact hcV1 ((le_of_card_eq_two_of_inf_ne_bot hcard_c hne) (Subgroup.mem_zpowers c))
  have hcH : c ∈ hz T V := hUH (hVU hcV)
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (Subgroup.zpowers_le.mpr hcH).trans hF.H_normalizes_V₁
  have hW1card : Nat.card ↥(Subgroup.zpowers c ⊔ fsuV1 T V) = 4 := by
    have := L32NSet14.card_sup_mul_card_inf hcN
    rw [hinf, Subgroup.card_bot, hcard_c, hF.card_V₁] at this
    omega
  have hW1T : T ≤ Subgroup.normalizer ((Subgroup.zpowers c ⊔ fsuV1 T V : Subgroup G) : Set G) := by
    intro t ht
    have htH := hTH ht
    rw [← conjSub_eq_self_iff]
    refine conjSub_eq_of_le ?_
    rw [conjSub_sup, conjSub_zpowers, conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ htH)]
    refine sup_le ?_ le_sup_right
    rw [Subgroup.zpowers_le]
    rw [show t * c * t⁻¹ = (t * c * t⁻¹ * c⁻¹) * c by group]
    exact mul_mem (Subgroup.mem_sup_right (hcT t ht)) (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers c))
  have hW1V : Subgroup.zpowers c ⊔ fsuV1 T V ≤ V :=
    sup_le (Subgroup.zpowers_le.mpr hcV) hV1V
  have hW1 : Subgroup.zpowers c ⊔ fsuV1 T V = V₂ :=
    unique1282 h1222 G T L V 3 (h.hyp1281One h13322 hMod) 2 _ _
      ⟨hW1V, by rw [hW1card]; norm_num, hW1T⟩
      ⟨hV2.2.1, by rw [hV2.2.2.2]; norm_num, hV2.2.2.1⟩
  have hcV2 : c ∈ V₂ := by
    rw [← hW1]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hV2P : V₂ ≤ P := by
    rw [← hW1]
    exact sup_le (Subgroup.zpowers_le.mpr hcP) le_sup_right
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  have hZU0 := N.zα_not_le_u0 hF h68 h
  have hidx2 := relIndex_eq_two_of_card hV2.1 hF.card_V₁ hV2.2.2.2
  have hZV2 : conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ := by
    intro y hy
    have hyP : y ∈ P := Subgroup.mem_sup_left (hZF hy)
    have hV2N : V₂ ≤ Subgroup.normalizer (u0 T V : Set G) :=
      (hV2.2.1.trans (hVU.trans hUH)).trans (hz_le_normalizer_u0 h hMod)
    have hy' := hZ hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV2N] at hy'
    obtain ⟨a, ha, u, hu, hau⟩ := hy'
    have haP : a ∈ P := hV2P ha
    have huP : u ∈ P := by
      rw [show u = a⁻¹ * y by rw [← hau]; group]
      exact mul_mem (inv_mem haP) hyP
    have huV1 : u ∈ fsuV1 T V := by
      rw [← hPU0]
      exact Subgroup.mem_inf.mpr ⟨huP, hu⟩
    rw [← hau]
    exact mul_mem ha (hV2.1 huV1)
  refine ⟨hZV2, ?_⟩
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hVU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  have hVU0card : Nat.card ↥(V ⊔ u0 T V) = 16 := by
    have := L32NSet14.card_sup_mul_card_inf hVN
    rw [inf_u0_eq h hMod h63 hF, hV8, h4, hF.card_V₁] at this
    omega
  have hPsup : P ⊔ u0 T V = V ⊔ u0 T V := by
    rw [hP, sup_assoc, sup_eq_right.mpr hV1U0, hFU0]
  have hPN : P ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hPU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  have hPcard : Nat.card ↥P = 8 := by
    have := L32NSet14.card_sup_mul_card_inf hPN
    rw [hPsup, hPU0, hVU0card, hF.card_V₁, h4] at this
    omega
  have hPVeq : P ⊓ V = V₂ := by
    refine le_antisymm (fun y hy => ?_) (le_inf hV2P hV2.2.1)
    obtain ⟨hyP, hyV⟩ := Subgroup.mem_inf.mp hy
    rcases hPV y hyP hyV with h1 | h1
    · exact hV2.1 h1
    · rw [show y = (y * c⁻¹) * c by group]
      exact mul_mem (hV2.1 h1) hcV2
  have hcomm : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V → a * b = b * a :=
    fun ha hb => F7.isElemAbelian_comm (isElemAbelian_fsuU_of h hMod) ha hb
  have hPNV : P ≤ Subgroup.normalizer (V : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [hcomm (hPU hy) (hVU hv), mul_inv_cancel_right]
      exact hv
    · intro hv
      have hvU : v ∈ fsuU T V := by
        have := mul_mem (mul_mem (inv_mem (hPU hy)) (hVU hv)) (hPU hy)
        rwa [show y⁻¹ * (y * v * y⁻¹) * y = v by group] at this
      rwa [hcomm (hPU hy) hvU, mul_inv_cancel_right] at hv
  have hPVcard : Nat.card ↥(P ⊔ V) = 16 := by
    have := L32NSet14.card_sup_mul_card_inf hPNV
    rw [hPVeq, hPcard, hV8, hV2.2.2.2] at this
    omega
  have hPVle : P ⊔ V ≤ V ⊔ u0 T V := sup_le (le_sup_left.trans hPsup.le) le_sup_left
  have hPVeq' : P ⊔ V = V ⊔ u0 T V :=
    Subgroup.eq_of_le_of_card_ge hPVle (by rw [hPVcard, hVU0card])
  rw [← hPVeq', hP, sup_assoc, sup_eq_right.mpr hV1V]

theorem zα_le_of_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hu0 : u0 T V = fsuV1 T V) {V₂ : Subgroup G}
    (hV2 : A6.IsV2 T V V₂) (hZ : conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ ⊔ u0 T V)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂ ∧
      ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ V = V ⊔ u0 T V := by
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hFU0 := N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  rw [hu0, sup_eq_left.mpr hV2.1] at hZ
  refine ⟨hZ, ?_⟩
  rw [hu0, sup_eq_left.mpr hV1V] at hFU0 ⊢
  exact sup_eq_right.mpr (le_sup_left.trans hFU0.le)

theorem lemma14_7_70_three_four (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2)
    (hZV2 : conjSub ((k : G) * g) (fsuV1 T V) ≤ V₂)
    (hFV : ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ V = V ⊔ u0 T V) :
    fsuU T V ⊓ conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) = V ⊔ u0 T V ∧
      V ⊔ u0 T V = ⁅fsuU T V, conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ⊔ V ∧
      ⁅fsuU T V, conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ⊔ V =
        ⁅fsuU T V, conjSub (k : G) (F8.Uγ V (hz T V) (g : G))⁆ ⊔ u0 T V ∧
      F8.b T V L (hz T V) = 3 ∧
      ∃ l ∈ L, conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) = conjSub l (fsuU T V) := by
  have h13322 := stmt13_3_2_two_of h1332
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  have hUeq := fsuU_eq_conjClosure_hz hMod h
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hA : conjSub (k : G)⁻¹⁻¹ (F8.A₁ (fsuV1 T V) (g : G)) ≤ V := by
    rw [inv_inv, F8.A₁, ← conjSub_mul]
    exact hZV2.trans hV2.2.1
  obtain ⟨hb3, l, hlL, hl⟩ :=
    lemma14_7_3_four S0 h13322 hMod hF N.setup rfl (inv_mem N.mem) hA
  rw [inv_inv, ← hUeq] at hl
  rw [uα_eq (g := g) (k := k) h hMod] at hl ⊢
  have hVW : V ≤ conjSub ((k : G) * g) (fsuU T V) := by
    rw [hl]
    calc V = conjSub l V := (conjSub_eq_self_iff.mpr (hLTV (Subgroup.mem_sup_left hlL))).symm
      _ ≤ conjSub l (fsuU T V) := conjSub_mono l (le_conjClosure V _)
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  have hFU0 := N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ
  have hFle := N.comm_le_inf h hMod hF
  have hWc : ∀ a ∈ conjSub ((k : G) * g) (fsuU T V), ∀ b ∈ conjSub ((k : G) * g) (fsuU T V),
      a * b = b * a := by
    intro a ha b hb
    rw [mem_conjSub] at ha hb
    have h1 := F7.isElemAbelian_comm (isElemAbelian_fsuU_of h hMod) ha hb
    set x := (k : G) * g
    calc a * b = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * (x⁻¹ * a * x)) * x⁻¹ := by rw [h1]
      _ = b * a := by group
  have hcap : fsuU T V ⊓ conjSub ((k : G) * g) (fsuU T V) = V ⊔ u0 T V := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨hyU, hyW⟩ := Subgroup.mem_inf.mp hy
      refine mem_sup_u0_of_comm_mem h hMod h63 hF h1222 h1332 h1334 hsR hsQ hyU ?_
      rw [hWc s hsW y hyW, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · rw [← hFV]
      exact sup_le hFle (le_inf (le_conjClosure V _) hVW)
  exact ⟨hcap, hFV.symm, hFV.trans hFU0.symm, hb3, l, hlL, hl⟩

end Not1471

end CFSG.Quasithin.H13.L32A
