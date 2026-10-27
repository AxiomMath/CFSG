module

public import CFSG.RankThree.GF2n.Stroth80.Sec311CoverSub
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def N0t (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (t : G) : Subgroup G :=
  ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t), conjSubgroup h (LB M Q B) ⊓ hc.CN t

theorem N0t_le_CN (hc : Ctx M Q Z B) (t : G) : N0t M Q Z B hc t ≤ hc.CN t :=
  iSup₂_le fun _ _ => inf_le_right

theorem Ctx.conj_LB_le_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {h : G}
    (hh : h ∈ Rt M (LB M Q B) t) : conjSubgroup h (LB M Q B) ≤ Rt M (LB M Q B) t := by
  intro y hy
  have hl : h⁻¹ * y * h ∈ LB M Q B := mem_conjSubgroup.mp hy
  have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
  rw [this]
  exact (Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem hh (le_Rt (M := M) (LB M Q B) ht hl))
    ((Rt M (LB M Q B) t).inv_mem hh)

theorem N0t_conj_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) {x : G} (hx : x ∈ N0t M Q Z B hc t) :
    r * x * r⁻¹ ∈ N0t M Q Z B hc t := by
  refine Subgroup.iSup_induction (fun h : G => ⨆ (_ : h ∈ Rt M (LB M Q B) t),
    conjSubgroup h (LB M Q B) ⊓ hc.CN t)
    (C := fun x => r * x * r⁻¹ ∈ N0t M Q Z B hc t) hx ?_ ?_ ?_
  · intro h x hx
    refine Subgroup.iSup_induction (fun (_ : h ∈ Rt M (LB M Q B) t) =>
      conjSubgroup h (LB M Q B) ⊓ hc.CN t)
      (C := fun x => r * x * r⁻¹ ∈ N0t M Q Z B hc t) hx ?_ ?_ ?_
    · intro hh x hxm
      have hrh : r * h ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).mul_mem hr hh
      refine Subgroup.mem_iSup_of_mem (r * h) (Subgroup.mem_iSup_of_mem hrh ⟨?_, ?_⟩)
      · show r * x * r⁻¹ ∈ conjSubgroup (r * h) (LB M Q B)
        rw [mem_conjSubgroup]
        have := mem_conjSubgroup.mp hxm.1
        have e : (r * h)⁻¹ * (r * x * r⁻¹) * (r * h) = h⁻¹ * x * h := by group
        rw [e]
        exact this
      · exact hc.CN_conj_mem ht hr hxm.2
    · simp
    · intro a b ha hb
      have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
  · simp
  · intro a b ha hb
    have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb

theorem N0t_comm_mem (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {h : G} (hh : h ∈ Rt M (LB M Q B) t) {x : G} (hx : x ∈ hc.CN t)
    {l : G} (hl : l ∈ conjSubgroup h (LB M Q B)) : ⁅x, l⁆ ∈ N0t M Q Z B hc t := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hlR : l ∈ Rt M (LB M Q B) t := hc.conj_LB_le_Rt hs.mem hh hl
  have hnorm := Subgroup.mem_normalizer_iff.mp (hc.CN_normalizes_conj_LB h35 hs.mem hh hx)
  refine Subgroup.mem_iSup_of_mem h (Subgroup.mem_iSup_of_mem hh ⟨?_, ?_⟩)
  · have e : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := commutatorElement_def x l
    rw [e]
    exact Subgroup.mul_mem _ ((hnorm l).mp hl) (Subgroup.inv_mem _ hl)
  · have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (hc.CN t).mul_mem hx (hc.CN_conj_mem hs.mem hlR ((hc.CN t).inv_mem hx))

theorem Ctx.mem_normalizer_LB_of_normalizer_LN (h34 : Stroth34Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hrn : r ∈ Subgroup.normalizer ((LB M Q B ⊔ hc.CN t : Subgroup G) : Set G)) :
    r ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hrM : r ∈ M := hc.Rt_le_M t hr
  refine (hc.mem_normalizer_LB_iff' hs.width hs.n_gt hs.noA2 hrM).mpr ?_
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hxC : x ∈ CQt Q Z (LB M Q B) := by rw [h35]; exact hx
  have hxV : x ∈ Vt M (LB M Q B) B Z t :=
    (sup_le (hc.B_le_Vt hs.mem) sec39_Z_le_Vt : B ⊔ Z ≤ Vt M (LB M Q B) B Z t) hx
  have hyV : r * x * r⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt hs.mem hr) x).mp hxV
  have hyQ : r * x * r⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hrM).1 x hxC.1
  have hZn : ∀ a ∈ M, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha) z).mp hz
  suffices hy : r * x * r⁻¹ ∈ CQt Q Z (LB M Q B) by
    rw [h35] at hy
    exact hy
  refine ⟨hyQ, fun l hl => ?_⟩
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hLN : LB M Q B ≤ Subgroup.normalizer (hc.CN t : Set G) := fun l hl =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hc.CN_conj_mem hs.mem (hLR hl) hy,
      fun hy => by
        have := hc.CN_conj_mem hs.mem ((Rt M (LB M Q B) t).inv_mem (hLR hl)) hy
        have e : l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y := by group
        rwa [e] at this⟩
  have hmem : r⁻¹ * l * r ∈ LB M Q B ⊔ hc.CN t := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrn) l).mp
      (Subgroup.mem_sup_left hl)
    simpa using this
  obtain ⟨l₁, hl₁, n₁, hn₁, hln⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN hmem
  have hl' : l = (r * l₁ * r⁻¹) * (r * n₁ * r⁻¹) := by
    have e : l = r * (r⁻¹ * l * r) * r⁻¹ := by group
    rw [e, ← hln]
    group
  have hn'N : r * n₁ * r⁻¹ ∈ hc.CN t := hc.CN_conj_mem hs.mem hr hn₁
  have hl'M : r * l₁ * r⁻¹ ∈ M := by
    have h1 : l₁ ∈ M := hc.LB_le_M hl₁
    exact M.mul_mem (M.mul_mem hrM h1) (M.inv_mem hrM)
  have h1 : ⁅r * n₁ * r⁻¹, r * x * r⁻¹⁆ ∈ Z := (Ctx.mem_CN.mp hn'N).2 _ hyV
  have h2 : ⁅r * l₁ * r⁻¹, r * x * r⁻¹⁆ ∈ Z := by
    have e : ⁅r * l₁ * r⁻¹, r * x * r⁻¹⁆ = r * ⁅l₁, x⁆ * r⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hZn r hrM _ (hxC.2 l₁ hl₁)
  have h3 : ⁅(r * l₁ * r⁻¹) * (r * n₁ * r⁻¹), r * x * r⁻¹⁆ =
      (r * l₁ * r⁻¹) * ⁅r * n₁ * r⁻¹, r * x * r⁻¹⁆ * (r * l₁ * r⁻¹)⁻¹ *
        ⁅r * l₁ * r⁻¹, r * x * r⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [hl', h3]
  exact Z.mul_mem (hZn _ hl'M _ h1) h2

@[expose] def Stroth311ConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B →
    Rt M (LB M Q B) t ≤ ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t), conjSubgroup h (LB M Q B)

@[expose] def Stroth311TorusStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B →
    ¬ Vt M (LB M Q B) B Z t ≤ QB B →
    ∃ τ ∈ Rt M (LB M Q B) t, τ ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      ∀ l ∈ LB M Q B, ⁅τ, l⁆ ∈ hc.CN t → l ∈ hc.CN t

theorem stroth311ElAb :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
      Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
      ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B →
      ∀ l ∈ LB M Q B, ∀ l' ∈ LB M Q B, ⁅l, l'⁆ ∈ hc.CN t ∧ l ^ 2 ∈ hc.CN t := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR l hl l' hl'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  exact ⟨hQN (Subgroup.commutator_le.mp hc.commutator_LB_le_Q l hl l' hl'),
    hQN (hc.sq_mem_Q_of_mem_LB hl)⟩

@[expose] def Stroth311RootOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (t : G), t ∈ LB M Q B → t ∉ Q → Rt M (LB M Q B) t ≠ LB M Q B →
    ¬ Vt M (LB M Q B) B Z t ≤ QB B →
    OmegaPlusNat hc t 2 → Nat.card Z ^ 2 ≤ (hc.CN t).relIndex (LB M Q B)

theorem Ctx.CN_le_N0t (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t)
    (hConj : Rt M (LB M Q B) t ≤ ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
      conjSubgroup h (LB M Q B))
    (hAb : ∀ l ∈ LB M Q B, ∀ l' ∈ LB M Q B, ⁅l, l'⁆ ∈ hc.CN t ∧ l ^ 2 ∈ hc.CN t)
    {τ : G} (hτR : τ ∈ Rt M (LB M Q B) t) (hτL : τ ∈ Subgroup.normalizer (LB M Q B : Set G))
    (hτ : ∀ l ∈ LB M Q B, ⁅τ, l⁆ ∈ hc.CN t → l ∈ hc.CN t)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) (b : ℕ)
    (hP : ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E) (π : E →* GL ι K),
      π.range = φ.range → π.ker = Y → Y ≤ Subgroup.center E → commutator E = ⊤ →
      ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) → b ≤ Nat.card A → Y = ⊥)
    (hb : b ≤ (hc.CN t).relIndex (LB M Q B)) : hc.CN t ≤ N0t M Q Z B hc t := by
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  refine le_of_perfect_cover_sub (Rt M (LB M Q B) t) (hc.CN t) (N0t M Q Z B hc t) (LB M Q B)
    (fun x hx => (Ctx.mem_CN.mp hx).1) (N0t_le_CN hc t) hLR
    (fun r hr n hn => N0t_conj_mem hc hs.mem hr hn) hConj
    (fun h hh n hn l hl => N0t_comm_mem h34 hc hs hh hn hl) ?_ hAb hτR hτL hτ
    (fun r hr hrn => hc.mem_normalizer_LB_of_normalizer_LN h34 hs hr hrn) φ hker b hP ?_
  · rintro x ⟨hxL, hxN⟩
    refine Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem
      ((Rt M (LB M Q B) t).one_mem) ⟨?_, hxN⟩)
    rw [conjSubgroup_one]
    exact hxL
  · rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hLR]
    exact hb

end CFSG.RankThree.GF2n.Stroth80
