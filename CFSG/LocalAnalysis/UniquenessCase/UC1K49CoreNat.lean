module

import all CFSG.LocalAnalysis.UniquenessCase.UC1K49Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreK
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement IsMulCommutative
open CFSG.GH74.Uniqueness.SU.SU5 (IsQ8D8)

variable {G : Type} [Group G] [Finite G]

open CFSG.ABGLocalTools (chiefAction chiefAction_mk chiefConj_apply_coe)

private theorem Lc_le_I49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (j : ℕ) : Lc L x j ≤ I :=
  conjugate_le_I h (by rw [hx]; exact (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) j)

private theorem chief_V_le49 {H X L Q I N M : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hch : HChief H N M) (V : ℕ → Subgroup G)
    (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) (j : ℕ) : V j ≤ N := by
  have hLjN : Lc L x j ≤ Subgroup.normalizer (N : Set G) :=
    ((Lc_le_I49 h hx j).trans (I_le_H h)).trans hch.2.1
  have hcomm_le : ⁅N, Lc L x j⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro n hn l hl
    have hmem : l * n * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hLjN hl) n).mp hn
    have : ⁅n, l⁆ = ⁅l, n⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [this]
    exact N.inv_mem (N.mul_mem hmem (N.inv_mem hn))
  rw [hV j]
  exact sup_le hcomm_le hch.1.le

private theorem chief_irr49 {H X L Q I N M : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hch : HChief H N M) (hNQ : N ≤ Q)
    (hshape : ChiefShape49 H L Q x N M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) →
      ∀ i : ℕ, i < 3 → ∀ Y : Subgroup G, M ≤ Y → Y ≤ V i →
        Lc L x i ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V i := by
  intro V hV i hi Y hMY hYV hNorm
  obtain ⟨_, _, _, hchief⟩ := hshape V hV
  have hYQ : ⁅Y, Q⁆ ≤ Y :=
    (Subgroup.commutator_mono (hYV.trans (chief_V_le49 h hx hch V hV i)) le_rfl).trans
      ((chief_q_trivial49 h hch hNQ).trans hMY)
  have hQN : Q ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hYQ
  exact (hchief i hi).2.2.2.2.2.2 Y hMY hYV (sup_le hNorm hQN)

private theorem comp_bar2_eq_one_iff49 {D : Subgroup G}
    (e : Bar2 D ≃* alternatingGroup (Fin 5)) (d : ↥D) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D))) d = 1 ↔
      d ∈ CFSG.pCore 2 ↥D := by
  rw [MonoidHom.comp_apply]
  constructor
  · intro hd
    refine (QuotientGroup.eq_one_iff _).mp (e.injective ?_)
    change e.toMonoidHom (QuotientGroup.mk' (CFSG.pCore 2 ↥D) d) = e.toMonoidHom 1
    rw [hd, map_one]
  · intro hd
    rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥D) d = 1 from (QuotientGroup.eq_one_iff _).mpr hd,
      map_one]

private theorem comm_mem_of_V49 {N M : Subgroup G} (V : ℕ → Subgroup G)
    (hN : N = V 0 ⊔ V 1 ⊔ V 2) (hMV : ∀ j, M ≤ V j) (hVN : ∀ j, V j ≤ N)
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ M) {d : G}
    (hVj : ∀ j : ℕ, j < 3 → ∀ n ∈ V j, ⁅n, d⁆ ∈ M) : ∀ n ∈ N, ⁅n, d⁆ ∈ M := by
  have hnorm : ∀ j k, j < k → k < 3 → V j ≤ Subgroup.normalizer (V k : Set G) := by
    intro j k hjk hk
    refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
    refine (Subgroup.commutator_le.mpr fun a ha b hb => hcomm a (hVN j ha) b (hVN k hb)).trans
      (hMV k)
  intro n hn
  rw [hN] at hn
  obtain ⟨a, ha, b2, hb2, rfl⟩ :=
    (mem_sup_of_le_normalizer (sup_le (hnorm 0 2 (by norm_num) (by norm_num))
      (hnorm 1 2 (by norm_num) (by norm_num)))).mp hn
  obtain ⟨a0, ha0, a1, ha1, rfl⟩ :=
    (mem_sup_of_le_normalizer (hnorm 0 1 (by norm_num) (by norm_num))).mp ha
  have h1c : a1 * ⁅b2, d⁆ * a1⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (hNM (hVN 1 ha1)) _).mp (hVj 2 (by norm_num) b2 hb2)
  have h0c : a0 * (a1 * ⁅b2, d⁆ * a1⁻¹ * ⁅a1, d⁆) * a0⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (hNM (hVN 0 ha0)) _).mp
      (M.mul_mem h1c (hVj 1 (by norm_num) a1 ha1))
  rw [mul_assoc, commutatorElement_mul_left_eq_conj_mul a0 (a1 * b2) d,
    commutatorElement_mul_left_eq_conj_mul a1 b2 d]
  exact M.mul_mem h0c (hVj 0 (by norm_num) a0 ha0)

private theorem chief_phi49 {H X L Q I N M : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hch : HChief H N M) (hNQ : N ≤ Q)
    (hIN : ¬ ⁅N, I⁆ ≤ M) (hshape : ChiefShape49 H L Q x N M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) → ∀ i : ℕ, i < 3 →
      ∃ φ : ↥(Lc L x i) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
        ∀ d : ↥(Lc L x i), φ d = 1 ↔ ∀ n ∈ V i, ⁅n, (d : G)⁆ ∈ M := by
  intro V hV i hi
  obtain ⟨hN_eq, _, htriv, _⟩ := hshape V hV
  have hmemX : x ^ i ∈ X := by
    rw [hx]; exact (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) i
  have hVN := chief_V_le49 h hx hch V hV
  obtain ⟨e⟩ : IsAlt (Bar2 (Lc L x i)) 5 := ((struct49 h).2.2.2.2.1 (x ^ i) hmemX).2.1
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lc L x i))),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun d => ?_⟩
  rw [comp_bar2_eq_one_iff49 e d, ← mem_pCoreOf_iff d.2,
    (((struct49 h).2.2.2.2.1 (x ^ i) hmemX).2.2.2).symm]
  have hNM : N ≤ Subgroup.normalizer (M : Set G) :=
    (hNQ.trans (Q_le_H49 h)).trans hch.2.2.1
  constructor
  · intro hdQ n hn
    exact (Subgroup.commutator_le.mp (chief_faithful49 h hch hNQ hIN).1) n (hVN i hn) d hdQ.2
  · intro hcent
    refine ⟨d.2, (chief_faithful49 h hch hNQ hIN).2 (d : G) (Lc_le_I49 h hx i d.2) ?_⟩
    refine comm_mem_of_V49 V hN_eq (fun j => ?_) hVN hNM hch.2.2.2.2.1 fun j hj n hn => ?_
    · rw [hV j]; exact le_sup_right
    · by_cases hji : j = i
      · subst hji; exact hcent n hn
      · exact (Subgroup.commutator_le.mp (htriv j i hj hi hji)) n hn d d.2

section Trace3

variable {W : Type} [CommGroup W]

private def fixSub (ξ : MulAut W) : Subgroup W where
  carrier := {w | ξ w = w}
  one_mem' := map_one _
  mul_mem' := fun {u v} hu hv => by
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    rw [map_mul, hu, hv]
  inv_mem' := fun {u} hu => by
    simp only [Set.mem_setOf_eq] at hu ⊢
    rw [map_inv, hu]

private theorem mem_fixSub {ξ : MulAut W} {w : W} : w ∈ fixSub ξ ↔ ξ w = w := Iff.rfl

private def trace3 (ξ : MulAut W) : W →* W :=
  MonoidHom.id W * (ξ : W →* W) * ((ξ : W →* W).comp (ξ : W →* W))

private theorem trace3_apply (ξ : MulAut W) (w : W) : trace3 ξ w = w * ξ w * ξ (ξ w) := rfl

private theorem trace3_ξ {ξ : MulAut W} (hc : ∀ w, ξ (ξ (ξ w)) = w) (w : W) :
    trace3 ξ (ξ w) = trace3 ξ w := by
  rw [trace3_apply, trace3_apply, hc]
  ac_rfl

private theorem ξ_trace3 {ξ : MulAut W} (hc : ∀ w, ξ (ξ (ξ w)) = w) (w : W) :
    ξ (trace3 ξ w) = trace3 ξ w := by
  rw [trace3_apply, map_mul, map_mul, hc]
  ac_rfl

private theorem trace3_of_fixed {ξ : MulAut W} (hsq : ∀ w : W, w * w = 1) {w : W}
    (hw : ξ w = w) : trace3 ξ w = w := by
  rw [trace3_apply, hw, hw, mul_assoc, hsq, mul_one]

private theorem trace3_comm {ξ κ : MulAut W} (hκ : ∀ w, κ (ξ w) = ξ (κ w)) (w : W) :
    κ (trace3 ξ w) = trace3 ξ (κ w) := by
  simp only [trace3_apply, map_mul, hκ]

private theorem trace3_eq_one {ξ : MulAut W} {P : ℕ → Subgroup W}
    (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1))
    (hdir : ∀ j, P j ⊓ (P (j + 1) ⊔ P (j + 2)) = ⊥) {j : ℕ} {p : W} (hp : p ∈ P j)
    (h1 : trace3 ξ p = 1) : p = 1 := by
  have hp1 : ξ p ∈ P (j + 1) := hstep j p hp
  have hp2 : ξ (ξ p) ∈ P (j + 2) := hstep (j + 1) _ hp1
  have h2 : p ∈ P (j + 1) ⊔ P (j + 2) := by
    have : p = (ξ p * ξ (ξ p))⁻¹ := by
      rw [trace3_apply, mul_assoc] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem_sup hp1 hp2)
  have h3 : p ∈ P j ⊓ (P (j + 1) ⊔ P (j + 2)) := ⟨hp, h2⟩
  rw [hdir j] at h3
  exact Subgroup.mem_bot.mp h3

private theorem exists_trace3_eq {ξ : MulAut W} {P : ℕ → Subgroup W}
    (hc : ∀ w, ξ (ξ (ξ w)) = w) (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1))
    (hper : ∀ j, P (j + 3) = P j) {j k : ℕ} (hk : k < 3) {p : W} (hp : p ∈ P (j + k)) :
    ∃ q ∈ P j, trace3 ξ q = trace3 ξ p := by
  interval_cases k
  · exact ⟨p, hp, rfl⟩
  · refine ⟨ξ (ξ p), ?_, by rw [trace3_ξ hc, trace3_ξ hc]⟩
    have := hstep _ _ (hstep _ _ hp)
    rwa [show j + 1 + 1 + 1 = j + 3 from rfl, hper] at this
  · refine ⟨ξ p, ?_, trace3_ξ hc p⟩
    have := hstep _ _ hp
    rwa [show j + 2 + 1 = j + 3 from rfl, hper] at this

private theorem card_map_of_injOn {A B : Type*} [Group A] [Group B] (f : A →* B)
    {P S : Subgroup A} (hP : ∀ x ∈ P, f x = 1 → x = 1) (hS : S ≤ P) :
    Nat.card (S.map f) = Nat.card S := by
  have hinj : Function.Injective (f.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hP x (hS x.2) hx)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  exact h.symm

private theorem map_trace3_eq_fixSub {ξ : MulAut W} {P : ℕ → Subgroup W}
    (hc : ∀ w, ξ (ξ (ξ w)) = w) (hsq : ∀ w : W, w * w = 1)
    (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1)) (hper : ∀ j, P (j + 3) = P j)
    (htop : ∀ j, P j ⊔ P (j + 1) ⊔ P (j + 2) = ⊤) (j : ℕ) :
    (P j).map (trace3 ξ) = fixSub ξ := by
  refine le_antisymm (by rintro _ ⟨p, _, rfl⟩; exact ξ_trace3 hc p) fun w hw => ?_
  have hw' : w ∈ P j ⊔ P (j + 1) ⊔ P (j + 2) := by rw [htop j]; trivial
  obtain ⟨uv, huv, t, ht, rfl⟩ := Subgroup.mem_sup.mp hw'
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp huv
  obtain ⟨qu, hqu, hqu'⟩ := exists_trace3_eq hc hstep hper (k := 0) (by norm_num) hu
  obtain ⟨qv, hqv, hqv'⟩ := exists_trace3_eq hc hstep hper (k := 1) (by norm_num) hv
  obtain ⟨qt, hqt, hqt'⟩ := exists_trace3_eq hc hstep hper (k := 2) (by norm_num) ht
  refine ⟨qu * qv * qt, (P j).mul_mem ((P j).mul_mem hqu hqv) hqt, ?_⟩
  show trace3 ξ (qu * qv * qt) = u * v * t
  rw [map_mul, map_mul, hqu', hqv', hqt', ← map_mul, ← map_mul]
  exact trace3_of_fixed hsq hw

private theorem card_eq_card_fixSub {ξ : MulAut W} {P : ℕ → Subgroup W}
    (hc : ∀ w, ξ (ξ (ξ w)) = w) (hsq : ∀ w : W, w * w = 1)
    (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1)) (hper : ∀ j, P (j + 3) = P j)
    (htop : ∀ j, P j ⊔ P (j + 1) ⊔ P (j + 2) = ⊤)
    (hdir : ∀ j, P j ⊓ (P (j + 1) ⊔ P (j + 2)) = ⊥) (j : ℕ) :
    Nat.card (P j) = Nat.card (fixSub ξ) := by
  rw [← map_trace3_eq_fixSub hc hsq hstep hper htop j]
  exact (card_map_of_injOn (trace3 ξ) (P := P j)
    (fun x hx h => trace3_eq_one hstep hdir hx h) le_rfl).symm

private theorem card_inf_fixSub_eq {ξ κ : MulAut W} {P : ℕ → Subgroup W}
    (hc : ∀ w, ξ (ξ (ξ w)) = w) (hsq : ∀ w : W, w * w = 1)
    (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1)) (hper : ∀ j, P (j + 3) = P j)
    (htop : ∀ j, P j ⊔ P (j + 1) ⊔ P (j + 2) = ⊤)
    (hdir : ∀ j, P j ⊓ (P (j + 1) ⊔ P (j + 2)) = ⊥) (hκ : ∀ w, κ (ξ w) = ξ (κ w)) (j : ℕ)
    (hκP : ∀ w ∈ P j, κ w ∈ P j) :
    Nat.card ↥(P j ⊓ fixSub κ) = Nat.card ↥(fixSub ξ ⊓ fixSub κ) := by
  have hmap : (P j ⊓ fixSub κ).map (trace3 ξ) = fixSub ξ ⊓ fixSub κ := by
    refine le_antisymm ?_ fun w ⟨hwξ, hwκ⟩ => ?_
    · rintro _ ⟨p, ⟨_, hp⟩, rfl⟩
      have hp' : κ p = p := hp
      exact ⟨ξ_trace3 hc p, show κ (trace3 ξ p) = trace3 ξ p by rw [trace3_comm hκ, hp']⟩
    · obtain ⟨p, hp, rfl⟩ := (map_trace3_eq_fixSub hc hsq hstep hper htop j).ge hwξ
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      have h1 : trace3 ξ (κ p * p⁻¹) = 1 := by
        rw [map_mul, map_inv, ← trace3_comm hκ, mem_fixSub.mp hwκ, mul_inv_cancel]
      have h2 := trace3_eq_one hstep hdir ((P j).mul_mem (hκP p hp) ((P j).inv_mem hp)) h1
      exact mul_inv_eq_one.mp h2
  rw [← hmap]
  exact (card_map_of_injOn (trace3 ξ) (P := P j)
    (fun x hx h => trace3_eq_one hstep hdir hx h) inf_le_left).symm

private theorem fix_add_of_comm {ξ κ : MulAut W} {P : ℕ → Subgroup W}
    (hc : ∀ w, ξ (ξ (ξ w)) = w) (hstep : ∀ j, ∀ w ∈ P j, ξ w ∈ P (j + 1))
    (hper : ∀ j, P (j + 3) = P j) (hκ : ∀ w, κ (ξ w) = ξ (κ w)) {j : ℕ}
    (hj : ∀ w ∈ P j, κ w = w) (m : ℕ) : ∀ w ∈ P (j + m), κ w = w := by
  induction m with
  | zero => exact hj
  | succ m ih =>
    intro w hw
    have h1 : ξ (ξ w) ∈ P (j + m) := by
      have h := hstep _ _ (hstep _ _ hw)
      rwa [show j + (m + 1) + 1 + 1 = (j + m) + 3 by omega, hper] at h
    have h2 : ξ (ξ (κ w)) = ξ (ξ w) := by rw [← hκ, ← hκ]; exact ih _ h1
    calc κ w = ξ (ξ (ξ (κ w))) := (hc _).symm
      _ = ξ (ξ (ξ w)) := by rw [h2]
      _ = w := hc w

end Trace3

private structure Sec49 (H N M : Subgroup G) where
  W : Type
  [comm : CommGroup W]
  [fin : Finite W]
  proj : ↥N →* W
  surj : Function.Surjective proj
  ker : proj.ker = M.subgroupOf N
  MN : M ≤ N
  NH : N ≤ H
  HN : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N
  HM : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M
  sq : ∀ w : W, w * w = 1
  a : G → MulAut W
  a_mul : ∀ g g' : G, g ∈ H → g' ∈ H → a (g * g') = a g * a g'
  a_proj : ∀ (g : G) (hg : g ∈ H) (n : ↥N),
    a g (proj n) = proj ⟨g * n * g⁻¹, HN g hg n n.2⟩

attribute [instance] Sec49.comm Sec49.fin

open scoped Classical in
private noncomputable def Sec49.ofChief {H N M : Subgroup G} (hch : HChief H N M)
    (hNH : N ≤ H) : Sec49 H N M :=
  letI : (M.subgroupOf N).Normal := hch.normal
  letI : CFSG.IsElementaryAbelian 2 (↥N ⧸ M.subgroupOf N) := hch.isElementaryAbelian
  { W := ↥N ⧸ M.subgroupOf N
    comm := { (inferInstance : Group (↥N ⧸ M.subgroupOf N)) with
      mul_comm := fun a b => mul_comm' a b }
    fin := inferInstance
    proj := QuotientGroup.mk' (M.subgroupOf N)
    surj := QuotientGroup.mk'_surjective _
    ker := QuotientGroup.ker_mk' _
    MN := hch.1.le
    NH := hNH
    HN := fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (hch.2.1 hg) n).mp hn
    HM := fun g hg m hm => (Subgroup.mem_normalizer_iff.mp (hch.2.2.1 hg) m).mp hm
    sq := by
      intro w
      induction w using QuotientGroup.induction_on with
      | H n =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa [pow_two] using hch.2.2.2.2.2.1 (n : G) n.2
    a := fun g => if hg : g ∈ H then chiefAction hch.2.1 hch.2.2.1 ⟨g, hg⟩ else 1
    a_mul := by
      intro g g' hg hg'
      rw [dif_pos (H.mul_mem hg hg'), dif_pos hg, dif_pos hg']
      have hmul : (⟨g * g', H.mul_mem hg hg'⟩ : ↥H) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
      rw [hmul]
      exact map_mul _ _ _
    a_proj := by
      intro g hg n
      rw [dif_pos hg]
      exact (chiefAction_mk hch.2.1 hch.2.2.1 ⟨g, hg⟩ n).trans
        (congrArg _ (Subtype.ext (chiefConj_apply_coe hch.2.1 _ _))) }

section SecAPI

variable {H N M : Subgroup G}

private def Sec49.img (S : Sec49 H N M) (T : Subgroup G) : Subgroup S.W :=
  (T.subgroupOf N).map S.proj

private theorem Sec49.mem_img (S : Sec49 H N M) {T : Subgroup G} {w : S.W} :
    w ∈ S.img T ↔ ∃ n : ↥N, (n : G) ∈ T ∧ S.proj n = w := by
  simp only [Sec49.img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

private theorem Sec49.proj_eq_one_iff (S : Sec49 H N M) {n : ↥N} :
    S.proj n = 1 ↔ (n : G) ∈ M := by
  rw [← MonoidHom.mem_ker, S.ker, Subgroup.mem_subgroupOf]

private theorem Sec49.proj_eq_iff (S : Sec49 H N M) {n n' : ↥N} :
    S.proj n = S.proj n' ↔ (n : G)⁻¹ * n' ∈ M := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, S.proj_eq_one_iff]
  rfl

private theorem Sec49.img_mono (S : Sec49 H N M) {T T' : Subgroup G} (h : T ≤ T') :
    S.img T ≤ S.img T' := by
  intro w hw
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
  exact S.mem_img.mpr ⟨n, h hn, rfl⟩

private theorem Sec49.img_eq_bot_iff (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N) :
    S.img T = ⊥ ↔ T ≤ M := by
  constructor
  · intro h t ht
    have h1 : S.proj ⟨t, hT ht⟩ ∈ S.img T := S.mem_img.mpr ⟨⟨t, hT ht⟩, ht, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact S.proj_eq_one_iff.mp h1
  · intro h
    refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    exact S.proj_eq_one_iff.mpr (h hn)

private theorem Sec49.img_M (S : Sec49 H N M) : S.img M = ⊥ :=
  (S.img_eq_bot_iff S.MN).mpr le_rfl

private theorem Sec49.img_N (S : Sec49 H N M) : S.img N = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, rfl⟩ := S.surj w
  exact S.mem_img.mpr ⟨n, n.2, rfl⟩

private theorem Sec49.img_sup (S : Sec49 H N M) {T T' : Subgroup G} (hT : T ≤ N)
    (hT' : T' ≤ N) : S.img (T ⊔ T') = S.img T ⊔ S.img T' := by
  rw [Sec49.img, Sec49.img, Sec49.img, Subgroup.subgroupOf_sup hT hT', Subgroup.map_sup]

private theorem Sec49.img_inf (S : Sec49 H N M) {T T' : Subgroup G} (hM : M ≤ T)
    (hM' : M ≤ T') : S.img (T ⊓ T') = S.img T ⊓ S.img T' := by
  refine le_antisymm (le_inf (S.img_mono inf_le_left) (S.img_mono inf_le_right)) ?_
  rintro w ⟨hw, hw'⟩
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
  obtain ⟨n', hn', hnn⟩ := S.mem_img.mp hw'
  have hm : (n : G)⁻¹ * n' ∈ M := S.proj_eq_iff.mp hnn.symm
  have hnT' : (n : G) ∈ T' := by
    have := T'.mul_mem hn' (T'.inv_mem (hM' hm))
    simpa using this
  exact S.mem_img.mpr ⟨n, ⟨hn, hnT'⟩, rfl⟩

private theorem Sec49.card_img (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N) :
    Nat.card (S.img T) = M.relIndex T := by
  have h := Subgroup.relIndex_ker (T.subgroupOf N) S.proj
  rw [S.ker, Subgroup.relIndex_subgroupOf hT] at h
  exact h.symm

private theorem Sec49.proj_mem_img_iff (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N)
    {n : ↥N} : S.proj n ∈ S.img T ↔ (n : G) ∈ T ⊔ M := by
  constructor
  · intro h
    obtain ⟨t, ht, htn⟩ := S.mem_img.mp h
    have hm : (t : G)⁻¹ * n ∈ M := S.proj_eq_iff.mp htn
    have := Subgroup.mul_mem_sup ht hm
    simpa using this
  · intro h
    have h1 : S.proj n ∈ S.img (T ⊔ M) := S.mem_img.mpr ⟨n, h, rfl⟩
    rwa [S.img_sup hT S.MN, S.img_M, sup_bot_eq] at h1

private theorem Sec49.a_one (S : Sec49 H N M) : S.a 1 = 1 := by
  have h := S.a_mul 1 1 H.one_mem H.one_mem
  simpa using h

private theorem Sec49.a_inv (S : Sec49 H N M) {g : G} (hg : g ∈ H) :
    S.a g⁻¹ = (S.a g)⁻¹ := by
  have h := S.a_mul g⁻¹ g (H.inv_mem hg) hg
  rw [inv_mul_cancel, S.a_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private def Sec49.stab (S : Sec49 H N M) (w : S.W) : Subgroup G where
  carrier := {g | g ∈ H ∧ S.a g w = w}
  one_mem' := ⟨H.one_mem, by rw [S.a_one]; rfl⟩
  mul_mem' := fun {g g'} hg hg' => ⟨H.mul_mem hg.1 hg'.1, by
    rw [S.a_mul g g' hg.1 hg'.1, MulAut.mul_apply, hg'.2, hg.2]⟩
  inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, by
    rw [S.a_inv hg.1]
    exact (MulEquiv.symm_apply_eq _).mpr hg.2.symm⟩

private def Sec49.fix (S : Sec49 H N M) (g : G) : Subgroup S.W := fixSub (S.a g)

private theorem Sec49.mem_fix (S : Sec49 H N M) {g : G} {w : S.W} :
    w ∈ S.fix g ↔ S.a g w = w := Iff.rfl

private theorem Sec49.a_eq_iff (S : Sec49 H N M) {g : G} (hg : g ∈ H) (n : ↥N) :
    S.a g (S.proj n) = S.proj n ↔ ⁅(n : G), g⁆ ∈ M := by
  rw [S.a_proj g hg n, S.proj_eq_iff]
  have key : (g * (n : G) * g⁻¹)⁻¹ * n = (n : G)⁻¹ * ⁅(n : G), g⁆ * n := by
    simp only [commutatorElement_def]
    group
  show (g * (n : G) * g⁻¹)⁻¹ * n ∈ M ↔ _
  rw [key]
  constructor
  · intro h
    have := S.HM n (S.NH n.2) _ h
    simpa [mul_assoc] using this
  · intro h
    have := S.HM n⁻¹ (H.inv_mem (S.NH n.2)) _ h
    simpa [mul_assoc] using this

private theorem mem_normalizer_inf' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

private theorem Sec49.mem_normalizer_M (S : Sec49 H N M) {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨S.HM g hg m, fun h => ?_⟩
  simpa [mul_assoc] using S.HM g⁻¹ (H.inv_mem hg) _ h

private theorem Sec49.proj_mem_fix (S : Sec49 H N M) {g : G} (hg : g ∈ H) (n : ↥N)
    (hc : (n : G) ∈ Subgroup.centralizer ({g} : Set G)) : S.proj n ∈ S.fix g := by
  rw [S.mem_fix, S.a_proj g hg n]
  congr 1
  apply Subtype.ext
  have h1 : g * (n : G) = n * g := Subgroup.mem_centralizer_iff.mp hc g rfl
  show g * (n : G) * g⁻¹ = n
  rw [h1, mul_inv_cancel_right]

private theorem Sec49.comm_mem_inf (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N) {g : G}
    (hg : g ∈ H) (hgT : g ∈ Subgroup.normalizer (T : Set G)) {n : ↥N} (hn : (n : G) ∈ T)
    (hf : S.a g (S.proj n) = S.proj n) : g * (n : G) * g⁻¹ * (n : G)⁻¹ ∈ T ⊓ M := by
  refine ⟨T.mul_mem ((Subgroup.mem_normalizer_iff.mp hgT _).mp hn) (T.inv_mem hn), ?_⟩
  have h1 : ⁅(n : G), g⁆ ∈ M := (S.a_eq_iff hg n).mp hf
  have h2 : ⁅(n : G), g⁆⁻¹ ∈ M := M.inv_mem h1
  rwa [commutatorElement_inv, commutatorElement_def] at h2

private theorem Sec49.exists_centralizer_rep (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N)
    (hT2 : IsPGroup 2 T) {g : G} (hg : g ∈ H) (hg3 : g ^ 3 = 1)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) {n : ↥N} (hn : (n : G) ∈ T)
    (hf : S.a g (S.proj n) = S.proj n) :
    ∃ c : ↥N, (c : G) ∈ T ⊓ Subgroup.centralizer ({g} : Set G) ∧ S.proj c = S.proj n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
  have hgD : Subgroup.zpowers g ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hgT
  have hgTM : g ∈ Subgroup.normalizer ((T ⊓ M : Subgroup G) : Set G) :=
    mem_normalizer_inf' hgT (S.mem_normalizer_M hg)
  have hTn : T ≤ Subgroup.normalizer ((T ⊓ M : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf' (Subgroup.le_normalizer ht) (S.mem_normalizer_M (S.NH (hT ht)))
  have hzp : Subgroup.zpowers g ≤ S.stab (S.proj n) := Subgroup.zpowers_le.mpr ⟨hg, hf⟩
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card T) := by
    rw [Nat.card_zpowers, hk]
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hg3)
  have hmem : (n : G) ∈ (T ⊓ Subgroup.centralizer (Subgroup.zpowers g : Set G)) ⊔ (T ⊓ M) :=
    (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff inf_le_left hTn hgD
      (Subgroup.zpowers_le.mpr hgTM) hcop inferInstance hn).mp fun d hd =>
      S.comm_mem_inf hT (hzp hd).1 (hgD hd) hn (hzp hd).2
  have hCn : T ⊓ Subgroup.centralizer (Subgroup.zpowers g : Set G) ≤
      Subgroup.normalizer ((T ⊓ M : Subgroup G) : Set G) := fun c hc => hTn hc.1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hmem
  obtain ⟨c, hc, m, hm, hcm⟩ := hmem
  have hcN : c ∈ N := hT hc.1
  refine ⟨⟨c, hcN⟩, ⟨hc.1, ?_⟩, ?_⟩
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers g)) hc.2
  · rw [S.proj_eq_iff]
    have : (c : G)⁻¹ * n = m := by rw [← hcm]; group
    show c⁻¹ * (n : G) ∈ M
    rw [this]
    exact hm.2

private theorem Sec49.img_inf_fix (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N)
    (hT2 : IsPGroup 2 T) {g : G} (hg : g ∈ H) (hg3 : g ^ 3 = 1)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    S.img T ⊓ S.fix g = S.img (T ⊓ Subgroup.centralizer ({g} : Set G)) := by
  ext w
  constructor
  · rintro ⟨hw, hwf⟩
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    obtain ⟨c, hc, hcn⟩ := S.exists_centralizer_rep hT hT2 hg hg3 hgT hn hwf
    exact S.mem_img.mpr ⟨c, hc, hcn⟩
  · intro hw
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    exact ⟨S.mem_img.mpr ⟨n, hn.1, rfl⟩, S.proj_mem_fix hg n hn.2⟩

private theorem Sec49.a_mem_img (S : Sec49 H N M) {T : Subgroup G} {g : G} (hg : g ∈ H)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) {w : S.W} (hw : w ∈ S.img T) :
    S.a g w ∈ S.img T := by
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
  rw [S.a_proj g hg n]
  exact S.mem_img.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp hgT _).mp hn, rfl⟩

private def Sec49.pre (S : Sec49 H N M) (Y : Subgroup S.W) : Subgroup G :=
  (Y.comap S.proj).map N.subtype

private theorem Sec49.mem_pre (S : Sec49 H N M) {Y : Subgroup S.W} {n : G} :
    n ∈ S.pre Y ↔ ∃ hn : n ∈ N, S.proj ⟨n, hn⟩ ∈ Y := by
  simp only [Sec49.pre, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hn, h⟩
    exact ⟨⟨n, hn⟩, h, rfl⟩

private theorem Sec49.le_pre (S : Sec49 H N M) (Y : Subgroup S.W) : M ≤ S.pre Y := fun m hm =>
  S.mem_pre.mpr ⟨S.MN hm, by rw [(S.proj_eq_one_iff).mpr hm]; exact Y.one_mem⟩

private theorem Sec49.img_pre (S : Sec49 H N M) (Y : Subgroup S.W) : S.img (S.pre Y) = Y := by
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    obtain ⟨hnN, h⟩ := S.mem_pre.mp hn
    exact h
  · intro hw
    obtain ⟨n, rfl⟩ := S.surj w
    exact S.mem_img.mpr ⟨n, S.mem_pre.mpr ⟨n.2, hw⟩, rfl⟩

private theorem Sec49.irr_img (S : Sec49 H N M) {T D : Subgroup G} (hMT : M ≤ T) (hT : T ≤ N)
    (hD : D ≤ H)
    (hirr : ∀ Y : Subgroup G, M ≤ Y → Y ≤ T →
      D ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = T)
    {Y : Subgroup S.W} (hY : Y ≤ S.img T) (hstab : ∀ l ∈ D, ∀ w ∈ Y, S.a l w ∈ Y) :
    Y = ⊥ ∨ Y = S.img T := by
  have hYT : S.pre Y ≤ T := by
    intro n hn
    obtain ⟨hnN, h⟩ := S.mem_pre.mp hn
    have := (S.proj_mem_img_iff hT).mp (hY h)
    rwa [sup_eq_left.mpr hMT] at this
  have key : ∀ l' ∈ D, ∀ y ∈ S.pre Y, l' * y * l'⁻¹ ∈ S.pre Y := by
    intro l' hl' y hy
    obtain ⟨hyN, hyY⟩ := S.mem_pre.mp hy
    refine S.mem_pre.mpr ⟨S.HN l' (hD hl') y hyN, ?_⟩
    have := hstab l' hl' _ hyY
    rwa [S.a_proj l' (hD hl') ⟨y, hyN⟩] at this
  have hnorm : D ≤ Subgroup.normalizer ((S.pre Y : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key l hl y, fun h => ?_⟩
    simpa [mul_assoc] using key l⁻¹ (D.inv_mem hl) _ h
  rcases hirr (S.pre Y) (S.le_pre Y) hYT hnorm with h | h
  · left
    rw [← S.img_pre Y, h, S.img_M]
  · right
    rw [← S.img_pre Y, h]

private theorem Sec49.a_cube (S : Sec49 H N M) {g : G} (hg : g ∈ H) (hg3 : g ^ 3 = 1)
    (w : S.W) : S.a g (S.a g (S.a g w)) = w := by
  have h : S.a g * (S.a g * S.a g) = 1 := by
    rw [← S.a_mul g g hg hg, ← S.a_mul g (g * g) hg (H.mul_mem hg hg), ← S.a_one,
      ← pow_three, hg3]
  have := congrArg (fun φ : MulAut S.W => φ w) h
  simpa [MulAut.mul_apply] using this

private theorem Sec49.a_comm (S : Sec49 H N M) {g g' : G} (hg : g ∈ H) (hg' : g' ∈ H)
    (hcomm : g * g' = g' * g) (w : S.W) : S.a g (S.a g' w) = S.a g' (S.a g w) := by
  have h := congrArg (fun y => S.a y w) hcomm
  simpa [S.a_mul g g' hg hg', S.a_mul g' g hg' hg, MulAut.mul_apply] using h

private theorem Sec49.fixes_img_iff (S : Sec49 H N M) {T : Subgroup G} (hT : T ≤ N) {g : G}
    (hg : g ∈ H) : (∀ w ∈ S.img T, S.a g w = w) ↔ ∀ n ∈ T, ⁅n, g⁆ ∈ M := by
  constructor
  · intro h n hn
    exact (S.a_eq_iff hg ⟨n, hT hn⟩).mp (h _ (S.mem_img.mpr ⟨⟨n, hT hn⟩, hn, rfl⟩))
  · intro h w hw
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    exact (S.a_eq_iff hg n).mpr (h n hn)

private def Sec49.kerOn (S : Sec49 H N M) (D : Subgroup G) (hD : D ≤ H) (Y : Subgroup S.W) :
    Subgroup G where
  carrier := {g | g ∈ D ∧ ∀ w ∈ Y, S.a g w = w}
  one_mem' := ⟨D.one_mem, fun w _ => by rw [S.a_one]; rfl⟩
  mul_mem' := fun {g g'} hg hg' => ⟨D.mul_mem hg.1 hg'.1, fun w hw => by
    rw [S.a_mul g g' (hD hg.1) (hD hg'.1), MulAut.mul_apply, hg'.2 w hw, hg.2 w hw]⟩
  inv_mem' := fun {g} hg => ⟨D.inv_mem hg.1, fun w hw => by
    rw [S.a_inv (hD hg.1)]
    exact (MulEquiv.symm_apply_eq _).mpr (hg.2 w hw).symm⟩

private theorem Sec49.mem_kerOn (S : Sec49 H N M) {D : Subgroup G} {hD : D ≤ H}
    {Y : Subgroup S.W} {g : G} : g ∈ S.kerOn D hD Y ↔ g ∈ D ∧ ∀ w ∈ Y, S.a g w = w := Iff.rfl

private theorem Sec49.le_normalizer_kerOn (S : Sec49 H N M) {D : Subgroup G} (hD : D ≤ H)
    {Y : Subgroup S.W} (hY : ∀ g ∈ D, ∀ w ∈ Y, S.a g w ∈ Y) :
    D ≤ Subgroup.normalizer (S.kerOn D hD Y : Set G) := by
  have key : ∀ g ∈ D, ∀ y ∈ S.kerOn D hD Y, g * y * g⁻¹ ∈ S.kerOn D hD Y := by
    intro g hg y hy
    refine ⟨D.mul_mem (D.mul_mem hg hy.1) (D.inv_mem hg), fun w hw => ?_⟩
    have h1 : S.a g⁻¹ w ∈ Y := hY g⁻¹ (D.inv_mem hg) w hw
    have h2 : S.a g (S.a g⁻¹ w) = w := by
      rw [← MulAut.mul_apply, ← S.a_mul g g⁻¹ (hD hg) (H.inv_mem (hD hg)), mul_inv_cancel,
        S.a_one]
      rfl
    rw [S.a_mul (g * y) g⁻¹ (H.mul_mem (hD hg) (hD hy.1)) (H.inv_mem (hD hg)),
      S.a_mul g y (hD hg) (hD hy.1), MulAut.mul_apply, MulAut.mul_apply, hy.2 _ h1, h2]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key l hl y, fun h => ?_⟩
  simpa [mul_assoc] using key l⁻¹ (D.inv_mem hl) _ h

end SecAPI

private structure Ctx49 (H X L Q I N M : Subgroup G) (x : G) (V : ℕ → Subgroup G) : Prop where
  setup : Setup49 H X L Q I
  gen : X = Subgroup.zpowers x
  chief : HChief H N M
  NQ : N ≤ Q
  NQM : ⁅N, Q⁆ ≤ M
  hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M
  dec : N = V 0 ⊔ V 1 ⊔ V 2
  dir : V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M
  triv : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M
  vchief : ∀ i : ℕ, i < 3 → HChief (Lc L x i ⊔ Q) (V i) M
  irr : ∀ i : ℕ, i < 3 → ∀ Y : Subgroup G, M ≤ Y → Y ≤ V i →
    Lc L x i ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V i
  phi : ∀ i : ℕ, i < 3 → ∃ φ : ↥(Lc L x i) →* alternatingGroup (Fin 5),
    Function.Surjective φ ∧ ∀ d : ↥(Lc L x i), φ d = 1 ↔ ∀ n ∈ V i, ⁅n, (d : G)⁆ ∈ M
  faith : ∀ g ∈ I, (∀ n ∈ N, ⁅n, g⁆ ∈ M) → g ∈ Q

private theorem Ctx49.ofShape {H X L Q I N M : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hch : HChief H N M) (hNQ : N ≤ Q) (hIN : ¬ ⁅N, I⁆ ≤ M)
    (hshape : ChiefShape49 H L Q x N M) (V : ℕ → Subgroup G)
    (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) : Ctx49 H X L Q I N M x V :=
  have hs := hshape V hV
  { setup := h, gen := hx, chief := hch, NQ := hNQ, NQM := chief_q_trivial49 h hch hNQ,
    hV := hV, dec := hs.1, dir := hs.2.1, triv := hs.2.2.1, vchief := hs.2.2.2,
    irr := chief_irr49 h hx hch hNQ hshape V hV,
    phi := chief_phi49 h hx hch hNQ hIN hshape V hV,
    faith := (chief_faithful49 h hch hNQ hIN).2 }

section Ctx49

variable {H X L Q I N M : Subgroup G} {x : G} {V : ℕ → Subgroup G}

private theorem Ctx49.x_mem (c : Ctx49 H X L Q I N M x V) : x ∈ X :=
  c.gen ▸ Subgroup.mem_zpowers x

private theorem Ctx49.x_H (c : Ctx49 H X L Q I N M x V) : x ∈ H := c.setup.X_le c.x_mem

private theorem Ctx49.x_cube (c : Ctx49 H X L Q I N M x V) : x ^ 3 = 1 := by
  rw [← orderOf_eq_three_of_zpowers c.gen c.setup.card_X]
  exact pow_orderOf_eq_one x

private theorem Ctx49.Q_H (c : Ctx49 H X L Q I N M x V) : Q ≤ H := Q_le_H49 c.setup

private theorem Ctx49.N_H (c : Ctx49 H X L Q I N M x V) : N ≤ H := c.NQ.trans c.Q_H

private theorem Ctx49.Q_two (c : Ctx49 H X L Q I N M x V) : IsPGroup 2 ↥Q := by
  rw [c.setup.Q_eq]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H

private theorem Ctx49.Lc_I (c : Ctx49 H X L Q I N M x V) (j : ℕ) : Lc L x j ≤ I :=
  Lc_le_I49 c.setup c.gen j

private theorem Ctx49.M_V (c : Ctx49 H X L Q I N M x V) (j : ℕ) : M ≤ V j := by
  rw [c.hV j]
  exact le_sup_right

private theorem Ctx49.V_N (c : Ctx49 H X L Q I N M x V) (j : ℕ) : V j ≤ N :=
  chief_V_le49 c.setup c.gen c.chief V c.hV j

private theorem Ctx49.V_two (c : Ctx49 H X L Q I N M x V) (j : ℕ) : IsPGroup 2 ↥(V j) :=
  c.Q_two.to_le ((c.V_N j).trans c.NQ)

private theorem Ctx49.Lc_period (c : Ctx49 H X L Q I N M x V) (j : ℕ) :
    Lc L x (j + 3) = Lc L x j := by
  rw [Lc, Lc, pow_add, c.x_cube, mul_one]

private theorem Ctx49.V_period (c : Ctx49 H X L Q I N M x V) (j : ℕ) : V (j + 3) = V j := by
  rw [c.hV, c.hV, c.Lc_period]

private theorem Ctx49.I_eq (c : Ctx49 H X L Q I N M x V) :
    I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2 := by
  rw [I_eq_sup_conjugates49 c.setup c.x_mem c.gen]
  simp only [Lc, pow_zero, pow_one, conjugate_one]

private theorem Ctx49.Lc_norm_V (c : Ctx49 H X L Q I N M x V) {i j : ℕ} (hi : i < 3)
    (hj : j < 3) : Lc L x j ≤ Subgroup.normalizer (V i : Set G) := by
  by_cases hij : j = i
  · subst hij
    exact le_sup_left.trans (c.vchief j hi).2.1
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((c.triv i j hi hj (Ne.symm hij)).trans (c.M_V i))

private theorem Ctx49.I_norm_V (c : Ctx49 H X L Q I N M x V) {i : ℕ} (hi : i < 3) :
    I ≤ Subgroup.normalizer (V i : Set G) := by
  rw [c.I_eq]
  exact sup_le (sup_le (c.Lc_norm_V hi (by norm_num)) (c.Lc_norm_V hi (by norm_num)))
    (c.Lc_norm_V hi (by norm_num))

private theorem Ctx49.conj_mem_V (c : Ctx49 H X L Q I N M x V) (j : ℕ) {n : G}
    (hn : n ∈ V j) : x⁻¹ * n * x⁻¹⁻¹ ∈ V (j + 1) := by
  have hN : N.map (MulAut.conj x⁻¹).toMonoidHom = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.chief.2.1 (H.inv_mem c.x_H))
  have hM : M.map (MulAut.conj x⁻¹).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.chief.2.2.1 (H.inv_mem c.x_H))
  have hL : (Lc L x j).map (MulAut.conj x⁻¹).toMonoidHom = Lc L x (j + 1) := by
    show CFSG.conjugate (CFSG.conjugate L (x ^ j)) x = CFSG.conjugate L (x ^ (j + 1))
    rw [conjugate_conjugate, pow_succ]
  have hmap : (V j).map (MulAut.conj x⁻¹).toMonoidHom = V (j + 1) := by
    rw [c.hV, c.hV, Subgroup.map_sup, Subgroup.map_commutator, hN, hM, hL]
  have : (MulAut.conj x⁻¹) n ∈ V (j + 1) := hmap ▸ Subgroup.mem_map_of_mem _ hn
  simpa [MulAut.conj_apply] using this

private theorem Ctx49.V_mod (c : Ctx49 H X L Q I N M x V) (j : ℕ) : V j = V (j % 3) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 3
    · rw [Nat.mod_eq_of_lt hj]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
      rw [c.V_period, ih k (by omega), Nat.add_mod_right]

private theorem Ctx49.V_top (c : Ctx49 H X L Q I N M x V) (j : ℕ) :
    V j ⊔ V (j + 1) ⊔ V (j + 2) = N := by
  rw [c.V_mod j, c.V_mod (j + 1), c.V_mod (j + 2)]
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · rw [h, show (j + 1) % 3 = 1 by omega, show (j + 2) % 3 = 2 by omega, c.dec]
  · rw [h, show (j + 1) % 3 = 2 by omega, show (j + 2) % 3 = 0 by omega, c.dec]
    ac_rfl
  · rw [h, show (j + 1) % 3 = 0 by omega, show (j + 2) % 3 = 1 by omega, c.dec]
    ac_rfl

private theorem Ctx49.V_dir (c : Ctx49 H X L Q I N M x V) (j : ℕ) :
    V j ⊓ (V (j + 1) ⊔ V (j + 2)) = M := by
  rw [c.V_mod j, c.V_mod (j + 1), c.V_mod (j + 2)]
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · rw [h, show (j + 1) % 3 = 1 by omega, show (j + 2) % 3 = 2 by omega]
    exact c.dir.1
  · rw [h, show (j + 1) % 3 = 2 by omega, show (j + 2) % 3 = 0 by omega, sup_comm]
    exact c.dir.2.1
  · rw [h, show (j + 1) % 3 = 0 by omega, show (j + 2) % 3 = 1 by omega]
    exact c.dir.2.2

end Ctx49

private structure Cyc49 {H N M : Subgroup G} (S : Sec49 H N M) (x : G)
    (V : ℕ → Subgroup G) : Prop where
  cube : ∀ w, S.a x⁻¹ (S.a x⁻¹ (S.a x⁻¹ w)) = w
  step : ∀ j, ∀ w ∈ S.img (V j), S.a x⁻¹ w ∈ S.img (V (j + 1))
  per : ∀ j, S.img (V (j + 3)) = S.img (V j)
  top : ∀ j, S.img (V j) ⊔ S.img (V (j + 1)) ⊔ S.img (V (j + 2)) = ⊤
  dir : ∀ j, S.img (V j) ⊓ (S.img (V (j + 1)) ⊔ S.img (V (j + 2))) = ⊥

private theorem Ctx49.cyc {H X L Q I N M : Subgroup G} {x : G} {V : ℕ → Subgroup G}
    (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) : Cyc49 S x V where
  cube := S.a_cube (H.inv_mem c.x_H) (by rw [inv_pow, c.x_cube, inv_one])
  step := fun j w hw => by
    obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
    rw [S.a_proj x⁻¹ (H.inv_mem c.x_H) n]
    exact S.mem_img.mpr ⟨_, c.conj_mem_V j hn, rfl⟩
  per := fun j => by rw [c.V_period]
  top := fun j => by
    rw [← S.img_sup (c.V_N _) (c.V_N _), ← S.img_sup (sup_le (c.V_N _) (c.V_N _)) (c.V_N _),
      c.V_top, S.img_N]
  dir := fun j => by
    rw [← S.img_sup (c.V_N _) (c.V_N _),
      ← S.img_inf (c.M_V _) ((c.M_V (j + 1)).trans le_sup_left), c.V_dir, S.img_M]

private structure KData49 (X I Q K E : Subgroup G) : Prop where
  K_I : K ≤ I
  K_cent : K ≤ Subgroup.centralizer (X : Set G)
  E_eq : E = K ⊓ Q
  K_E : K ≤ Subgroup.normalizer (E : Set G)
  comm_E : ∀ m ∈ Q ⊓ Subgroup.centralizer (X : Set G), ∀ k ∈ K, ⁅m, k⁆ ∈ E
  q8d8 : IsQ8D8 E
  card_Z : Nat.card ↥(E ⊓ Subgroup.centralizer (E : Set G)) = 2
  KZ : ⁅K, E ⊓ Subgroup.centralizer (E : Set G)⁆ = ⊥
  inv : ∀ Y : Subgroup G, Y ≤ E → K ≤ Subgroup.normalizer (Y : Set G) →
    Y = ⊥ ∨ Y = E ⊓ Subgroup.centralizer (E : Set G) ∨ Y = E
  ord3 : ∀ z ∈ K, orderOf z = 3 → Nat.card ↥(E ⊓ Subgroup.centralizer ({z} : Set G)) = 8
  card_K : Nat.card K = 60 * Nat.card E

private theorem KI_le_centralizer_inf49 (X I : Subgroup G) :
    KI X I ≤ Subgroup.centralizer (X : Set G) ⊓ I := by
  rw [KI]
  exact CFSG.Quasithin.perfectCore_le _

private theorem card_KI49 {X I Q : Subgroup G} (halt : IsAlt (Bar2 (KI X I)) 5)
    (hpc : KI X I ⊓ Q = CFSG.Open.pCoreOf 2 (KI X I)) :
    Nat.card ↥(KI X I) = 60 * Nat.card ↥(KI X I ⊓ Q) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(KI X I))
  have h2 : Nat.card (↥(KI X I) ⧸ CFSG.pCore 2 ↥(KI X I)) = 60 := card_bar2_L halt
  have h3 : Nat.card ↥(CFSG.Open.pCoreOf 2 (KI X I)) = Nat.card ↥(CFSG.pCore 2 ↥(KI X I)) :=
    Subgroup.card_subtype (KI X I) (CFSG.pCore 2 ↥(KI X I))
  rw [hpc, h3, h1, h2]

private theorem kdata49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (hK : KI49 X I) {A : Subgroup G} (hA : XReg49 X A) (hAI : A ≤ I) :
    KData49 X I Q (KI X I) (KI X I ⊓ Q) := by
  obtain ⟨hperf, halt, hpc, -, -, hcomm⟩ := kbasic49 h hA hAI
  obtain ⟨V, -, hKV, hVq8, hVpc, hZ2, hKZ, hinv, -, hord⟩ := kmodel49 hI hK hperf
  obtain rfl : V = KI X I ⊓ Q := hVpc.trans hpc.symm
  refine ⟨?_, ?_, rfl, hKV, fun m hm k hk => ?_, hVq8, hZ2, hKZ, hinv, hord, ?_⟩
  · exact (KI_le_centralizer_inf49 X I).trans inf_le_right
  · exact (KI_le_centralizer_inf49 X I).trans inf_le_left
  · exact Subgroup.commutator_le.mp hcomm m hm k hk
  · exact card_KI49 halt hpc

private theorem relIndex_sup_of_le_normalizer {K C : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (C : Set G)) : C.relIndex (K ⊔ C) = C.relIndex K := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hK
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient K C hK).toEquiv).symm

private theorem sup_eq_of_relIndex_eq {K L C I : Subgroup G}
    (hI : I ≤ Subgroup.normalizer (C : Set G)) (hK : K ≤ I) (hLC : I = L ⊔ C)
    (h : C.relIndex K = C.relIndex L) : K ⊔ C = I := by
  have hC : C ≤ I := hLC ▸ le_sup_right
  have hL : L ≤ I := hLC ▸ le_sup_left
  have h1 : C.relIndex I = C.relIndex L := by
    rw [hLC]
    exact relIndex_sup_of_le_normalizer (hL.trans hI)
  have h2 : C.relIndex (K ⊔ C) * (K ⊔ C).relIndex I = C.relIndex I :=
    Subgroup.relIndex_mul_relIndex C (K ⊔ C) I le_sup_right (sup_le hK hC)
  rw [relIndex_sup_of_le_normalizer (hK.trans hI), h, ← h1] at h2
  have hne : 0 < C.relIndex I := Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card C I) Nat.card_pos
  have h3 : (K ⊔ C).relIndex I = 1 := Nat.eq_of_mul_eq_mul_left hne (h2.trans (mul_one _).symm)
  exact le_antisymm (sup_le hK hC) (Subgroup.relIndex_eq_one.mp h3)

section Action

variable {H X L Q I N M K E : Subgroup G} {x : G} {V : ℕ → Subgroup G}

private theorem Ctx49.N_two (c : Ctx49 H X L Q I N M x V) : IsPGroup 2 ↥N :=
  c.Q_two.to_le c.NQ

private theorem Ctx49.I_H (c : Ctx49 H X L Q I N M x V) : I ≤ H := I_le_H c.setup

private theorem mem_centralizer_zpowers_iff' {x g : G} :
    g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) ↔ g * x = x * g := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_singleton_iff]

private theorem Ctx49.mem_centralizer_X_iff (c : Ctx49 H X L Q I N M x V) {g : G} :
    g ∈ Subgroup.centralizer (X : Set G) ↔ g * x⁻¹ = x⁻¹ * g := by
  rw [c.gen, mem_centralizer_zpowers_iff']
  exact ⟨fun h => (Commute.inv_right (show Commute g x from h)).eq,
    fun h => by simpa using (Commute.inv_right (show Commute g x⁻¹ from h)).eq⟩

private theorem Ctx49.a_mem_P (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {i : ℕ}
    (hi : i < 3) {g : G} (hg : g ∈ I) {w : S.W} (hw : w ∈ S.img (V i)) :
    S.a g w ∈ S.img (V i) :=
  S.a_mem_img (c.I_H hg) (c.I_norm_V hi hg) hw

private theorem Ctx49.a_triv_of_ne (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {i j : ℕ}
    (hi : i < 3) (hj : j < 3) (hij : i ≠ j) {g : G} (hg : g ∈ Lc L x j) {w : S.W}
    (hw : w ∈ S.img (V i)) : S.a g w = w := by
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
  exact (S.a_eq_iff (c.I_H (c.Lc_I j hg)) n).mpr
    (c.triv i j hi hj hij (Subgroup.commutator_mem_commutator hn hg))

private theorem Ctx49.a_nontrivial (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {i : ℕ}
    (hi : i < 3) : ∃ l ∈ Lc L x i, ∃ w ∈ S.img (V i), S.a l w ≠ w := by
  obtain ⟨φ, hφs, hφk⟩ := c.phi i hi
  obtain ⟨u, hu⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  obtain ⟨d, rfl⟩ := hφs u
  have hne : ¬ ∀ n ∈ V i, ⁅n, (d : G)⁆ ∈ M := fun h => hu ((hφk d).mpr h)
  push Not at hne
  obtain ⟨n, hn, hnM⟩ := hne
  refine ⟨d, d.2, S.proj ⟨n, c.V_N i hn⟩, S.mem_img.mpr ⟨_, hn, rfl⟩, fun h => hnM ?_⟩
  exact (S.a_eq_iff (c.I_H (c.Lc_I i d.2)) ⟨n, c.V_N i hn⟩).mp h

private theorem Ctx49.fixes_P_of_fixes_P (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M)
    {i j : ℕ} (hi : i < 3) (hj : j < 3) {k : G} (hkH : k ∈ H) (hkx : k * x⁻¹ = x⁻¹ * k)
    (hk : ∀ w ∈ S.img (V i), S.a k w = w) : ∀ w ∈ S.img (V j), S.a k w = w := by
  have hcyc := c.cyc S
  have hV : V j = V (i + (j + 3 - i) % 3) := by
    rw [c.V_mod j, c.V_mod (i + (j + 3 - i) % 3)]
    congr 1
    omega
  rw [hV]
  exact fix_add_of_comm (P := fun j => S.img (V j)) hcyc.cube hcyc.step hcyc.per
    (fun w => S.a_comm hkH (H.inv_mem c.x_H) hkx w) hk _

private theorem Ctx49.I_eq_Lc_sup (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {i : ℕ}
    (hi : i < 3) : I = Lc L x i ⊔ S.kerOn I c.I_H (S.img (V i)) := by
  have hle : ∀ j, j < 3 → Lc L x j ≤ Lc L x i ⊔ S.kerOn I c.I_H (S.img (V i)) := by
    intro j hj
    by_cases hij : j = i
    · subst hij
      exact le_sup_left
    · refine le_trans (fun g hg => ?_) le_sup_right
      exact ⟨c.Lc_I j hg, fun w hw => c.a_triv_of_ne S hi hj (Ne.symm hij) hg hw⟩
  refine le_antisymm (c.I_eq.le.trans (sup_le (sup_le (hle 0 (by norm_num))
    (hle 1 (by norm_num))) (hle 2 (by norm_num)))) (sup_le (c.Lc_I i) fun g hg => hg.1)

private theorem Ctx49.K_inf_kerOn (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) : K ⊓ S.kerOn I c.I_H (S.img (V i)) = E := by
  refine le_antisymm ?_ fun e he => ?_
  · rintro k ⟨hkK, hkI, hk⟩
    have hkH := c.I_H hkI
    have hall : ∀ j, j < 3 → ∀ n ∈ V j, ⁅n, k⁆ ∈ M := fun j hj n hn =>
      (S.fixes_img_iff (c.V_N j) hkH).mp (c.fixes_P_of_fixes_P S hi hj hkH
        (c.mem_centralizer_X_iff.mp (kd.K_cent hkK)) hk) n hn
    have hNM : N ≤ Subgroup.normalizer (M : Set G) := c.N_H.trans c.chief.2.2.1
    have hN := comm_mem_of_V49 V c.dec c.M_V c.V_N hNM c.chief.2.2.2.2.1 hall
    rw [kd.E_eq]
    exact ⟨hkK, c.faith k hkI hN⟩
  · rw [kd.E_eq] at he
    refine ⟨he.1, kd.K_I he.1, (S.fixes_img_iff (c.V_N i) (c.I_H (kd.K_I he.1))).mpr fun n hn => ?_⟩
    exact c.NQM (Subgroup.commutator_mem_commutator (c.V_N i hn) he.2)

private theorem KData49.E_K (kd : KData49 X I Q K E) : E ≤ K := kd.E_eq ▸ inf_le_left

private theorem Ctx49.relIndex_kerOn_K (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) :
    (S.kerOn I c.I_H (S.img (V i))).relIndex K = 60 := by
  have h1 : (S.kerOn I c.I_H (S.img (V i))).relIndex K = E.relIndex K := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, c.K_inf_kerOn kd S hi]
  have h2 := Subgroup.relIndex_mul_card (H := E) (K := K)
  rw [inf_eq_left.mpr kd.E_K, kd.card_K] at h2
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

private theorem Ctx49.relIndex_kerOn_Lc (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M)
    {i : ℕ} (hi : i < 3) : (S.kerOn I c.I_H (S.img (V i))).relIndex (Lc L x i) = 60 := by
  obtain ⟨φ, hφs, hφk⟩ := c.phi i hi
  have hker : (S.kerOn I c.I_H (S.img (V i))).subgroupOf (Lc L x i) = φ.ker := by
    ext d
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hφk d, S.mem_kerOn,
      S.fixes_img_iff (c.V_N i) (c.I_H (c.Lc_I i d.2))]
    exact ⟨fun h => h.2, fun h => ⟨c.Lc_I i d.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs,
    Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private theorem Ctx49.transfer (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) :
    ∀ l ∈ Lc L x i, ∃ k ∈ K, ∀ w ∈ S.img (V i), S.a l w = S.a k w := by
  intro l hl
  have hnorm := S.le_normalizer_kerOn c.I_H fun g hg w hw => c.a_mem_P S hi hg hw
  have hsup : K ⊔ S.kerOn I c.I_H (S.img (V i)) = I :=
    sup_eq_of_relIndex_eq hnorm kd.K_I (c.I_eq_Lc_sup S hi)
      ((c.relIndex_kerOn_K kd S hi).trans (c.relIndex_kerOn_Lc S hi).symm)
  have hlI : l ∈ K ⊔ S.kerOn I c.I_H (S.img (V i)) := by
    rw [hsup]
    exact c.Lc_I i hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (kd.K_I.trans hnorm)]
    at hlI
  obtain ⟨k, hk, y, hy, rfl⟩ := hlI
  refine ⟨k, hk, fun w hw => ?_⟩
  rw [S.a_mul k y (c.I_H (kd.K_I hk)) (c.I_H hy.1), MulAut.mul_apply, hy.2 w hw]

private theorem Ctx49.K_norm_EN (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E) {k : G}
    (hk : k ∈ K) : k ∈ Subgroup.normalizer ((E ⊓ N : Subgroup G) : Set G) :=
  mem_normalizer_inf' (kd.K_E hk) (c.chief.2.1 (c.I_H (kd.K_I hk)))

private theorem Ctx49.K_comm_xinv (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    {k : G} (hk : k ∈ K) : k * x⁻¹ = x⁻¹ * k :=
  c.mem_centralizer_X_iff.mp (kd.K_cent hk)

private theorem Ctx49.K_trivial_mod (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {k : G} (hk : k ∈ K) {w : S.W} (hw : w ∈ S.fix x⁻¹) :
    S.a k w * w⁻¹ ∈ S.img (E ⊓ N) := by
  have hxH : x⁻¹ ∈ H := H.inv_mem c.x_H
  have hw' : w ∈ S.img N ⊓ S.fix x⁻¹ := ⟨by rw [S.img_N]; trivial, hw⟩
  rw [S.img_inf_fix le_rfl c.N_two hxH (by rw [inv_pow, c.x_cube, inv_one])
    (c.chief.2.1 hxH)] at hw'
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw'
  have hkH : k ∈ H := c.I_H (kd.K_I hk)
  have hnQ : (n : G) ∈ Q ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨c.NQ n.2, c.mem_centralizer_X_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hn.2)⟩
  have hE : k * (n : G) * k⁻¹ * (n : G)⁻¹ ∈ E := by
    have h := E.inv_mem (kd.comm_E _ hnQ k hk)
    rwa [commutatorElement_inv] at h
  refine S.mem_img.mpr ⟨⟨k * n * k⁻¹, S.HN k hkH n n.2⟩ * n⁻¹, ⟨hE, N.mul_mem
    (S.HN k hkH n n.2) (N.inv_mem n.2)⟩, ?_⟩
  rw [map_mul, map_inv, S.a_proj k hkH n]

private theorem Ctx49.img_EN_le_fix (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) : S.img (E ⊓ N) ≤ S.fix x⁻¹ := by
  intro w hw
  obtain ⟨n, hn, rfl⟩ := S.mem_img.mp hw
  exact S.proj_mem_fix (H.inv_mem c.x_H) n (Subgroup.mem_centralizer_singleton_iff.mpr
    (c.K_comm_xinv kd (kd.E_K hn.1)))

private theorem Ctx49.Y_stable (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) :
    ∀ l ∈ Lc L x i, ∀ w ∈ S.img (V i) ⊓ (S.img (E ⊓ N)).comap (trace3 (S.a x⁻¹)),
      S.a l w ∈ S.img (V i) ⊓ (S.img (E ⊓ N)).comap (trace3 (S.a x⁻¹)) := by
  intro l hl w ⟨hwP, hwF⟩
  obtain ⟨k, hk, hlk⟩ := c.transfer kd S hi l hl
  have hkH : k ∈ H := c.I_H (kd.K_I hk)
  refine ⟨c.a_mem_P S hi (c.Lc_I i hl) hwP, ?_⟩
  show trace3 (S.a x⁻¹) (S.a l w) ∈ S.img (E ⊓ N)
  rw [hlk w hwP, ← trace3_comm (fun u => S.a_comm hkH (H.inv_mem c.x_H) (c.K_comm_xinv kd hk) u)]
  exact S.a_mem_img hkH (c.K_norm_EN kd hk) hwF

private theorem Ctx49.L_trivial_of_Y_bot (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3)
    (hY : S.img (V i) ⊓ (S.img (E ⊓ N)).comap (trace3 (S.a x⁻¹)) = ⊥) :
    ∀ l ∈ Lc L x i, ∀ w ∈ S.img (V i), S.a l w = w := by
  intro l hl w hw
  obtain ⟨k, hk, hlk⟩ := c.transfer kd S hi l hl
  have hkH : k ∈ H := c.I_H (kd.K_I hk)
  have hq : S.a k w * w⁻¹ ∈ S.img (V i) ⊓ (S.img (E ⊓ N)).comap (trace3 (S.a x⁻¹)) := by
    refine ⟨(S.img (V i)).mul_mem (c.a_mem_P S hi (kd.K_I hk) hw) ((S.img (V i)).inv_mem hw), ?_⟩
    show trace3 (S.a x⁻¹) (S.a k w * w⁻¹) ∈ S.img (E ⊓ N)
    rw [map_mul, map_inv, ← trace3_comm
      (fun u => S.a_comm hkH (H.inv_mem c.x_H) (c.K_comm_xinv kd hk) u)]
    exact c.K_trivial_mod kd S hk (ξ_trace3 (c.cyc S).cube w)
  rw [hY, Subgroup.mem_bot, mul_inv_eq_one] at hq
  rw [hlk w hw, hq]

private theorem Ctx49.fix_eq_img (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) : S.fix x⁻¹ = S.img (E ⊓ N) := by
  refine le_antisymm ?_ (c.img_EN_le_fix kd S)
  have hcyc := c.cyc S
  rcases S.irr_img (c.M_V i) (c.V_N i) ((c.Lc_I i).trans c.I_H) (c.irr i hi) inf_le_left
    (c.Y_stable kd S hi) with hY | hY
  · obtain ⟨l, hl, w, hw, hne⟩ := c.a_nontrivial S hi
    exact absurd (c.L_trivial_of_Y_bot kd S hi hY l hl w hw) hne
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := (map_trace3_eq_fixSub (P := fun j => S.img (V j)) hcyc.cube S.sq
      hcyc.step hcyc.per hcyc.top i).ge hw
    have hp' : p ∈ S.img (V i) ⊓ (S.img (E ⊓ N)).comap (trace3 (S.a x⁻¹)) := by rw [hY]; exact hp
    exact hp'.2

private theorem Ctx49.card_P_eq_relIndex (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) :
    Nat.card (S.img (V i)) = M.relIndex (E ⊓ N) := by
  have hcyc := c.cyc S
  rw [card_eq_card_fixSub (P := fun j => S.img (V j)) hcyc.cube S.sq hcyc.step hcyc.per
    hcyc.top hcyc.dir i]
  change Nat.card ↥(S.fix x⁻¹) = _
  rw [c.fix_eq_img kd S hi]
  exact S.card_img inf_le_right

private theorem Ctx49.three_le_card (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {i : ℕ}
    (hi : i < 3) : 3 ≤ Nat.card (S.img (V i)) := by
  obtain ⟨l, hl, w, hw, hne⟩ := c.a_nontrivial S hi
  have h1 : w ≠ 1 := fun h => hne (by rw [h, map_one])
  have h2 : S.a l w ≠ 1 := fun h => h1 ((MulEquiv.map_eq_one_iff _).mp h)
  have hsub : ({1, w, S.a l w} : Set S.W) ⊆ (S.img (V i) : Set S.W) := by
    rintro _ (rfl | rfl | rfl)
    · exact (S.img (V i)).one_mem
    · exact hw
    · exact c.a_mem_P S hi (c.Lc_I i hl) hw
  have h3 : ({1, w, S.a l w} : Set S.W).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, w, S.a l w, h1.symm, h2.symm, hne.symm, rfl⟩
  have h4 : Nat.card ↥(S.img (V i)) = (S.img (V i) : Set S.W).ncard := Nat.card_coe_set_eq _
  have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

private theorem Ctx49.false_of_E_inf_M_bot (c : Ctx49 H X L Q I N M x V)
    (kd : KData49 X I Q K E) (hEN : E ≤ N) (h0 : E ⊓ M = ⊥) : False := by
  have hbot : ⁅E, E⁆ = ⊥ := by
    refine eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun e he f hf => ?_)
    have h1 : ⁅e, f⁆ ∈ M := c.chief.2.2.2.2.1 e (hEN he) f (hEN hf)
    have h2 : ⁅e, f⁆ ∈ E := by
      simp only [commutatorElement_def]
      exact E.mul_mem (E.mul_mem (E.mul_mem he hf) (E.inv_mem he)) (E.inv_mem hf)
    have h3 : ⁅e, f⁆ ∈ E ⊓ M := ⟨h2, h1⟩
    rwa [h0] at h3
  exact isQ8D8_not_isMulCommutative kd.q8d8 ((Subgroup.commutator_self_eq_bot_iff (H := E)).mp hbot)

private theorem Ctx49.classify (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) :
    E ≤ N ∧ E ⊓ M = E ⊓ Subgroup.centralizer (E : Set G) := by
  have h3 := c.three_le_card S hi
  have hrel := c.card_P_eq_relIndex kd S hi
  have hK0 : K ≤ Subgroup.normalizer ((E ⊓ M : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf' (kd.K_E hk) (S.mem_normalizer_M (c.I_H (kd.K_I hk)))
  rcases kd.inv (E ⊓ N) inf_le_left (fun k hk => c.K_norm_EN kd hk) with h1 | h1 | h1
  · rw [h1, Subgroup.relIndex_bot_right] at hrel
    omega
  · rw [h1] at hrel
    have h2 : M.relIndex (E ⊓ Subgroup.centralizer (E : Set G)) ∣ 2 :=
      kd.card_Z ▸ Subgroup.relIndex_dvd_card _ _
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have hEN : E ≤ N := inf_eq_left.mp h1
    refine ⟨hEN, ?_⟩
    rcases kd.inv (E ⊓ M) inf_le_left hK0 with h0 | h0 | h0
    · exact (c.false_of_E_inf_M_bot kd hEN h0).elim
    · exact h0
    · rw [h1, Subgroup.relIndex_eq_one.mpr (inf_eq_left.mp h0)] at hrel
      omega

private theorem Ctx49.card_P (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) : Nat.card (S.img (V i)) = 16 := by
  obtain ⟨hEN, hEM⟩ := c.classify kd S hi
  rw [c.card_P_eq_relIndex kd S hi, inf_eq_left.mpr hEN, ← Subgroup.inf_relIndex_right M E,
    inf_comm M E, hEM]
  have h := Subgroup.relIndex_mul_card (H := E ⊓ Subgroup.centralizer (E : Set G)) (K := E)
  rw [inf_eq_left.mpr (inf_le_left : E ⊓ Subgroup.centralizer (E : Set G) ≤ E), kd.card_Z,
    kd.q8d8.facts.1] at h
  omega

private theorem Sec49.a_mul₃ (S : Sec49 H N M) {g₀ g₁ g₂ : G} (h₀ : g₀ ∈ H) (h₁ : g₁ ∈ H)
    (h₂ : g₂ ∈ H) (w : S.W) : S.a (g₀ * g₁ * g₂) w = S.a g₀ (S.a g₁ (S.a g₂ w)) := by
  rw [S.a_mul (g₀ * g₁) g₂ (H.mul_mem h₀ h₁) h₂, S.a_mul g₀ g₁ h₀ h₁]
  rfl

private theorem Sec49.inf_fix_eq_of_act_eq (S : Sec49 H N M) {P : Subgroup S.W} {g g' : G}
    (h : ∀ w ∈ P, S.a g w = S.a g' w) : P ⊓ S.fix g = P ⊓ S.fix g' := by
  ext w
  constructor
  · rintro ⟨hw, hf⟩
    have hf' : S.a g w = w := hf
    exact ⟨hw, show S.a g' w = w by rw [← h w hw]; exact hf'⟩
  · rintro ⟨hw, hf⟩
    have hf' : S.a g' w = w := hf
    exact ⟨hw, show S.a g w = w by rw [h w hw]; exact hf'⟩

private theorem Sec49.relIndex_sup_centralizer (S : Sec49 H N M) {T : Subgroup G} (hMT : M ≤ T)
    (hT : T ≤ N) (hT2 : IsPGroup 2 T) {g : G} (hg : g ∈ H) (hg3 : g ^ 3 = 1)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) :
    ((T ⊓ Subgroup.centralizer ({g} : Set G)) ⊔ M).relIndex T * Nat.card ↥(S.img T ⊓ S.fix g) =
      M.relIndex T := by
  have hC : (T ⊓ Subgroup.centralizer ({g} : Set G)) ⊔ M ≤ T := sup_le inf_le_left hMT
  have h1 := Subgroup.relIndex_mul_relIndex M ((T ⊓ Subgroup.centralizer ({g} : Set G)) ⊔ M) T
    le_sup_right hC
  have h2 : S.img ((T ⊓ Subgroup.centralizer ({g} : Set G)) ⊔ M) =
      S.img (T ⊓ Subgroup.centralizer ({g} : Set G)) := by
    rw [S.img_sup (inf_le_left.trans hT) S.MN, S.img_M, sup_bot_eq]
  rw [S.img_inf_fix hT hT2 hg hg3 hgT, ← h2, S.card_img (hC.trans hT), mul_comm]
  exact h1

private theorem KData49.Z_le_centralizer (kd : KData49 X I Q K E) {z : G} (hz : z ∈ K) :
    E ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro u hu
  have h : ⁅z, u⁆ ∈ (⊥ : Subgroup G) := kd.KZ ▸ Subgroup.commutator_mem_commutator hz hu
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm

private theorem KData49.relIndex_inf_cent (kd : KData49 X I Q K E)
    (hEM : E ⊓ M = E ⊓ Subgroup.centralizer (E : Set G)) {z : G} (hz : z ∈ K)
    (hz3 : orderOf z = 3) : M.relIndex (E ⊓ Subgroup.centralizer ({z} : Set G)) = 4 := by
  have hZ : E ⊓ M ≤ Subgroup.centralizer ({z} : Set G) := hEM.le.trans (kd.Z_le_centralizer hz)
  have hZle : E ⊓ M ≤ E ⊓ Subgroup.centralizer ({z} : Set G) := le_inf inf_le_left hZ
  have h1 : M ⊓ (E ⊓ Subgroup.centralizer ({z} : Set G)) = E ⊓ M := by
    rw [show M ⊓ (E ⊓ Subgroup.centralizer ({z} : Set G)) =
      (E ⊓ M) ⊓ Subgroup.centralizer ({z} : Set G) by ac_rfl]
    exact inf_eq_left.mpr hZ
  have h3 : M.relIndex (E ⊓ Subgroup.centralizer ({z} : Set G)) =
      (E ⊓ M).relIndex (E ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← Subgroup.inf_relIndex_right M (E ⊓ Subgroup.centralizer ({z} : Set G)), h1]
  have hcard : Nat.card ↥(E ⊓ M) = 2 := by rw [hEM]; exact kd.card_Z
  have h2 := Subgroup.relIndex_mul_card (H := E ⊓ M)
    (K := E ⊓ Subgroup.centralizer ({z} : Set G))
  rw [inf_eq_left.mpr hZle, hcard, kd.ord3 z hz hz3] at h2
  omega

private theorem Ctx49.card_P_inf_fix (c : Ctx49 H X L Q I N M x V) (kd : KData49 X I Q K E)
    (S : Sec49 H N M) {i : ℕ} (hi : i < 3) {z : G} (hz : z ∈ K) (hz3 : orderOf z = 3) :
    Nat.card ↥(S.img (V i) ⊓ S.fix z) = 4 := by
  have hcyc := c.cyc S
  have hzH : z ∈ H := c.I_H (kd.K_I hz)
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have h1 := card_inf_fixSub_eq (P := fun j => S.img (V j)) (κ := S.a z) hcyc.cube S.sq
    hcyc.step hcyc.per hcyc.top hcyc.dir
    (fun w => S.a_comm hzH (H.inv_mem c.x_H) (c.K_comm_xinv kd hz) w) i
    fun w hw => c.a_mem_P S hi (kd.K_I hz) hw
  obtain ⟨hEN, hEM⟩ := c.classify kd S hi
  change Nat.card ↥(S.img (V i) ⊓ fixSub (S.a z)) = 4
  rw [h1]
  change Nat.card ↥(S.fix x⁻¹ ⊓ S.fix z) = 4
  rw [c.fix_eq_img kd S hi, S.img_inf_fix inf_le_right (c.N_two.to_le inf_le_right) hzH hz3'
    (c.K_norm_EN kd hz), S.card_img (inf_le_left.trans inf_le_right), inf_eq_left.mpr hEN]
  exact kd.relIndex_inf_cent hEM hz hz3

private theorem Ctx49.act_z_eq_d (c : Ctx49 H X L Q I N M x V) (S : Sec49 H N M) {A : Subgroup G}
    {a n : G} (hd : XAData X L I x A a n) {i : ℕ} (hi : i < 3) {w : S.W}
    (hw : w ∈ S.img (V i)) :
    S.a (a * cj x a * cj (x ^ 2) a) w = S.a (cj (x ^ i) a) w := by
  have hg0 : a ∈ Lc L x 0 := by
    rw [Lc, pow_zero, conjugate_one]
    exact hd.a_mem
  have hg1 : cj x a ∈ Lc L x 1 := by
    rw [Lc, pow_one]
    exact conjugate_cj L a x hd.a_mem
  have hg2 : cj (x ^ 2) a ∈ Lc L x 2 := conjugate_cj L a (x ^ 2) hd.a_mem
  rw [S.a_mul₃ (c.I_H (c.Lc_I 0 hg0)) (c.I_H (c.Lc_I 1 hg1)) (c.I_H (c.Lc_I 2 hg2))]
  interval_cases i
  · rw [c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg2 hw,
      c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg1 hw]
    simp [cj]
  · rw [c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg2 hw,
      c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg0 (c.a_mem_P S hi (c.Lc_I 1 hg1) hw)]
    simp
  · rw [c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg1 (c.a_mem_P S hi (c.Lc_I 2 hg2) hw),
      c.a_triv_of_ne S hi (by norm_num) (by norm_num) hg0 (c.a_mem_P S hi (c.Lc_I 2 hg2) hw)]

end Action

private theorem orderOf_cj (g a : G) : orderOf (cj g a) = orderOf a := by
  have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
  simpa [MulAut.conj_apply] using h

private theorem gen_mem_A {X L I A : Subgroup G} {x a n : G} (hd : XAData X L I x A a n) :
    a ∈ A ∧ cj x a ∈ A ∧ cj (x ^ 2) a ∈ A :=
  ⟨hd.gen ▸ Subgroup.subset_closure (by simp), hd.gen ▸ Subgroup.subset_closure (by simp),
    hd.gen ▸ Subgroup.subset_closure (by simp)⟩

private theorem z_mem_A {X L I A : Subgroup G} {x a n : G} (hd : XAData X L I x A a n) :
    a * cj x a * cj (x ^ 2) a ∈ A :=
  A.mul_mem (A.mul_mem (gen_mem_A hd).1 (gen_mem_A hd).2.1) (gen_mem_A hd).2.2

private theorem z_mem_Z49 {X L I A : Subgroup G} {x a n : G} (hx : X = Subgroup.zpowers x)
    (hx3 : x ^ 3 = 1) (hd : XAData X L I x A a n) : a * cj x a * cj (x ^ 2) a ∈ Z49 X A := by
  haveI := hd.reg.2.1.1
  obtain ⟨haA, hbA, hcA⟩ := gen_mem_A hd
  refine ⟨z_mem_A hd, ?_⟩
  show a * cj x a * cj (x ^ 2) a ∈ Subgroup.centralizer (X : Set G)
  rw [hx, mem_centralizer_zpowers_iff']
  have hc2 : cj (x ^ 2) a = cj x (cj x a) := by rw [cj_mul, ← sq]
  have h1 : cj x (a * cj x a * cj (x ^ 2) a) = a * cj x a * cj (x ^ 2) a := by
    have h2 : cj x a * cj (x ^ 2) a * a = a * (cj x a * cj (x ^ 2) a) :=
      congrArg Subtype.val (mul_comm' (⟨cj x a * cj (x ^ 2) a, A.mul_mem hbA hcA⟩ : ↥A)
        ⟨a, haA⟩)
    have h3 : cj x (cj (x ^ 2) a) = a := by rw [hc2, cj_pow_three x a hx3]
    rw [cj_mul_cj, cj_mul_cj, ← hc2, h3, mul_assoc a]
    exact h2
  simp only [cj] at h1
  calc _ = x * (x⁻¹ * (a * cj x a * cj (x ^ 2) a) * x) := by group
    _ = _ := by rw [h1]

private theorem orderOf_z {X L I A : Subgroup G} {x a n : G} (hd : XAData X L I x A a n) :
    orderOf (a * cj x a * cj (x ^ 2) a) = 3 := by
  have h3 : (a * cj x a * cj (x ^ 2) a) ^ 3 = 1 := hd.reg.2.1.2 _ (z_mem_A hd)
  have hne : a * cj x a * cj (x ^ 2) a ≠ 1 := by
    intro h1
    have h2 : cj n (a * cj x a * cj (x ^ 2) a) = a⁻¹ * cj x a * cj (x ^ 2) a := by
      rw [cj_mul_cj, cj_mul_cj, hd.inv_a, hd.fix_b, hd.fix_c]
    have h4 : a⁻¹ * cj x a * cj (x ^ 2) a = a * cj x a * cj (x ^ 2) a := by
      rw [← h2, h1]
      simp [cj]
    have h5 : a⁻¹ = a := mul_right_cancel (mul_right_cancel h4)
    have h6 : a ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h5.symm
    have h7 := Nat.le_of_dvd (by norm_num) (hd.ord ▸ orderOf_dvd_of_pow_eq_one h6)
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

private theorem chief_index49 {H X L Q I N M : Subgroup G} (hI : Inputs49) (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) (hK : KI49 X I) {A : Subgroup G} {a n : G}
    (hd : XAData X L I x A a n) (hch : HChief H N M) (hNQ : N ≤ Q) (hIN : ¬ ⁅N, I⁆ ≤ M)
    (hshape : ChiefShape49 H L Q x N M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) → ∀ i : ℕ, i < 3 →
      M.relIndex (V i) = 16 := by
  intro V hV i hi
  have c := Ctx49.ofShape h hx hch hNQ hIN hshape V hV
  have kd := kdata49 hI h hK hd.reg hd.A_le
  rw [← (Sec49.ofChief hch c.N_H).card_img (c.V_N i)]
  exact c.card_P kd _ hi

private theorem chief_order3_49 {H X L Q I A N M : Subgroup G} (hI : Inputs49)
    (h : Setup49 H X L Q I) {x a n : G} (hx : X = Subgroup.zpowers x) (hK : KI49 X I)
    (hd : XAData X L I x A a n) (hch : HChief H N M) (hNQ : N ≤ Q)
    (hIN : ¬ ⁅N, I⁆ ≤ M) (hshape : ChiefShape49 H L Q x N M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) → ∀ i : ℕ, i < 3 →
      ∃ d ∈ Lc L x i, orderOf d = 3 ∧
        ((V i ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ M).relIndex (V i) = 4 := by
  intro V hV i hi
  have c := Ctx49.ofShape h hx hch hNQ hIN hshape V hV
  have kd := kdata49 hI h hK hd.reg hd.A_le
  let S := Sec49.ofChief hch c.N_H
  have hdL : cj (x ^ i) a ∈ Lc L x i := conjugate_cj L a (x ^ i) hd.a_mem
  have hzK : a * cj x a * cj (x ^ 2) a ∈ KI X I :=
    (kbasic49 h hd.reg hd.A_le).2.2.2.1 (z_mem_Z49 hx c.x_cube hd)
  have hd3 : orderOf (cj (x ^ i) a) = 3 := (orderOf_cj _ _).trans hd.ord
  refine ⟨cj (x ^ i) a, hdL, hd3, ?_⟩
  have h1 := S.relIndex_sup_centralizer (c.M_V i) (c.V_N i) (c.V_two i)
    (c.I_H (c.Lc_I i hdL)) (by rw [← hd3]; exact pow_orderOf_eq_one _)
    (c.I_norm_V hi (c.Lc_I i hdL))
  have h2 : Nat.card ↥(S.img (V i) ⊓ S.fix (cj (x ^ i) a)) = 4 := by
    rw [S.inf_fix_eq_of_act_eq fun w hw => (c.act_z_eq_d S hd hi hw).symm]
    exact c.card_P_inf_fix kd S hi hzK (orderOf_z hd)
  have h16 : M.relIndex (V i) = 16 := (S.card_img (c.V_N i)).symm.trans (c.card_P kd S hi)
  rw [h2, h16] at h1
  omega

theorem chief_nat49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hK : KI49 X I) {A : Subgroup G} {a n : G}
    (hd : XAData X L I x A a n) {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q)
    (hIN : ¬ ⁅N, I⁆ ≤ M) (hshape : ChiefShape49 H L Q x N M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) →
      ∀ i : ℕ, i < 3 → NatA5Sec (Lc L x i) (V i) M := by
  intro V hV i hi
  obtain ⟨_, _, _, hchief⟩ := hshape V hV
  have hMle : M ≤ V i := by rw [hV i]; exact le_sup_right
  have hDN : Lc L x i ≤ Subgroup.normalizer (V i : Set G) :=
    le_sup_left.trans (hchief i hi).2.1
  have hDM : Lc L x i ≤ Subgroup.normalizer (M : Set G) := by
    have hLiI : Lc L x i ≤ I := by
      have hxpow : x ^ i ∈ X := by
        rw [hx]
        exact (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) i
      exact conjugate_le_I h hxpow
    exact (hLiI.trans (I_le_H h)).trans (hch.2.2.1)
  have hV2 : IsPGroup 2 ↥(V i) := by
    have hQ2 : IsPGroup 2 ↥Q := by
      rw [h.Q_eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    exact hQ2.to_le ((chief_V_le49 h hx hch V hV i).trans hNQ)
  have hab : ∀ a ∈ V i, ∀ b ∈ V i, ⁅a, b⁆ ∈ M := (hchief i hi).2.2.2.2.1
  have hsq : ∀ a ∈ V i, a ^ 2 ∈ M := (hchief i hi).2.2.2.2.2.1
  have hirr : ∀ Y : Subgroup G, M ≤ Y → Y ≤ V i →
      Lc L x i ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V i :=
    chief_irr49 h hx hch hNQ hshape V hV i hi
  have hphi := chief_phi49 h hx hch hNQ hIN hshape V hV i hi
  have hidx := chief_index49 hI h hx hK hd hch hNQ hIN hshape V hV i hi
  have hd3 := chief_order3_49 hI h hx hK hd hch hNQ hIN hshape V hV i hi
  exact hI.2.2 G (Lc L x i) (V i) M hMle hV2 hDN hDM hab hsq hidx hirr hphi hd3

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
