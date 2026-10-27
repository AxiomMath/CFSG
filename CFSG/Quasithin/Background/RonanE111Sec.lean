module

public import CFSG.Quasithin.Background.RonanE111Wr
public import CFSG.Quasithin.EmptyFaithful.E111RMain

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G]

structure SecData (M XM YM : Subgroup G) (ℒ : Set (Subgroup G)) : Prop where
  SM : SemisimpleMod M XM YM ℒ
  nonempty : ℒ.Nonempty
  X_Y : XM ≤ Subgroup.normalizer (YM : Set G)
  M_X : M ≤ Subgroup.normalizer (XM : Set G)
  M_Y : M ≤ Subgroup.normalizer (YM : Set G)
  Ysolv : Group.IsSolvable ↥YM

variable [Finite G]

theorem sec_normalizer_of_conj_mem {L Y : Subgroup G} (hYn : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y)
    {a : G} (ha : a ∈ L) : a ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hYn a ha y hy, fun hy => ?_⟩
  have h := hYn a⁻¹ (L.inv_mem ha) _ hy
  simpa [mul_assoc] using h

theorem sec_commutator_sup_le {L A Y : Subgroup G} (hAL : A ≤ L)
    (hYn : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) (hLA : L ≤ A ⊔ Y) :
    ⁅L, L⁆ ≤ ⁅A, A⁆ ⊔ Y := by
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := fun a ha =>
    sec_normalizer_of_conj_mem hYn (hAL ha)
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have ha' : a ∈ Y ⊔ A := by rw [sup_comm]; exact hLA ha
  have hb' : b ∈ Y ⊔ A := by rw [sup_comm]; exact hLA hb
  obtain ⟨y₁, hy₁, x₁, hx₁, rfl⟩ := E111R.exists_mul_of_mem_sup hAN ha'
  obtain ⟨y₂, hy₂, x₂, hx₂, rfl⟩ := E111R.exists_mul_of_mem_sup hAN hb'
  obtain ⟨c, hc⟩ : ∃ c : G, c = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := ⟨_, rfl⟩
  have hcA : c ∈ ⁅A, A⁆ := by
    rw [hc, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hx₁ hx₂
  have hcL : c ∈ L := hAL (E111R.commutator_le_self A hcA)
  have hu₁ : x₁ * y₂ * x₁⁻¹ ∈ Y := hYn x₁ (hAL hx₁) y₂ hy₂
  have hu₂ : x₂ * y₁⁻¹ * x₂⁻¹ ∈ Y := hYn x₂ (hAL hx₂) y₁⁻¹ (Y.inv_mem hy₁)
  have hu₃ : c * (x₂ * y₁⁻¹ * x₂⁻¹) * c⁻¹ ∈ Y := hYn c hcL _ hu₂
  have hu₄ : c * y₂⁻¹ * c⁻¹ ∈ Y := hYn c hcL _ (Y.inv_mem hy₂)
  have hz : y₁ * (x₁ * y₂ * x₁⁻¹) * (c * (x₂ * y₁⁻¹ * x₂⁻¹) * c⁻¹) * (c * y₂⁻¹ * c⁻¹) ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hu₁) hu₃) hu₄
  have hkey : ⁅y₁ * x₁, y₂ * x₂⁆ = y₁ * (x₁ * y₂ * x₁⁻¹) * (c * (x₂ * y₁⁻¹ * x₂⁻¹) * c⁻¹) *
      (c * y₂⁻¹ * c⁻¹) * c := by
    subst hc
    rw [commutatorElement_def]
    group
  rw [hkey]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hcA)

theorem sec_conj_mem_sup {L C Y : Subgroup G} (hCL : C ≤ L)
    (hYn : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) (hCn : ∀ l ∈ L, ∀ c ∈ C, l * c * l⁻¹ ∈ C)
    {l : G} (hl : l ∈ L) {x : G} (hx : x ∈ C ⊔ Y) : l * x * l⁻¹ ∈ C ⊔ Y := by
  have hCN : C ≤ Subgroup.normalizer (Y : Set G) := fun c hc =>
    sec_normalizer_of_conj_mem hYn (hCL hc)
  rw [sup_comm] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := E111R.exists_mul_of_mem_sup hCN hx
  have e : l * (y * c) * l⁻¹ = (l * y * l⁻¹) * (l * c * l⁻¹) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup (hYn l hl y hy) (hCn l hl c hc)

theorem sec_le_commutator_sup {L Y : Subgroup G} (hYL : Y ≤ L)
    (hYn : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y)
    (hsimple : ∀ N : Subgroup G, Y ≤ N → N ≤ L → (N.subgroupOf L).Normal → N = Y ∨ N = L)
    (hnab : ¬ ⁅L, L⁆ ≤ Y) : L ≤ ⁅L, L⁆ ⊔ Y := by
  have hCL : ⁅L, L⁆ ≤ L := E111R.commutator_le_self L
  have hCn : ∀ l ∈ L, ∀ c ∈ ⁅L, L⁆, l * c * l⁻¹ ∈ ⁅L, L⁆ := by
    intro l hl c hc
    have hc' : c ∈ derivedSeriesOf L 1 := hc
    have hmem : (MulAut.conj l : G →* G) c ∈ (derivedSeriesOf L 1).map (MulAut.conj l : G →* G) :=
      Subgroup.mem_map_of_mem _ hc'
    rw [map_conj_derivedSeriesOf (Subgroup.le_normalizer hl) 1] at hmem
    exact hmem
  have hNL : ⁅L, L⁆ ⊔ Y ≤ L := sup_le hCL hYL
  have hnorm : ((⁅L, L⁆ ⊔ Y).subgroupOf L).Normal :=
    normal_subgroupOf_of_conj hNL fun s hs n hn => sec_conj_mem_sup hCL hYn hCn hs hn
  rcases hsimple (⁅L, L⁆ ⊔ Y) le_sup_right hNL hnorm with h | h
  · exact absurd (le_sup_left.trans h.le) hnab
  · exact h.ge

theorem key_le_perfectCore_sup {M XM YM : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : SecData M XM YM ℒ) {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ) :
    L₁ ≤ perfectCore L₁ ⊔ YM := by
  have hL₁XM : L₁ ≤ XM := hS.SM.le_D L₁ hL₁
  have hYn : ∀ l ∈ L₁, ∀ y ∈ YM, l * y * l⁻¹ ∈ YM := fun l hl y hy =>
    (Subgroup.mem_normalizer_iff.mp (hS.X_Y (hL₁XM hl)) y).mp hy
  have hstep := sec_le_commutator_sup (hS.SM.Y_le L₁ hL₁) hYn (hS.SM.simple L₁ hL₁)
    (hS.SM.nonab L₁ hL₁)
  have hind : ∀ n : ℕ, L₁ ≤ derivedSeriesOf L₁ n ⊔ YM := by
    intro n
    induction n with
    | zero => rw [derivedSeriesOf_zero]; exact le_sup_left
    | succ n ih =>
      have h1 := sec_commutator_sup_le (derivedSeriesOf_le L₁ n) hYn ih
      rw [derivedSeriesOf_succ]
      exact hstep.trans (sup_le h1 le_sup_right)
  obtain ⟨n, hn⟩ := exists_perfectCore_eq L₁
  have h := hind n
  rwa [← hn n le_rfl] at h

theorem sec_conjSub_sup (e : G) (A B : Subgroup G) :
    A1b.conjSub e (A ⊔ B) = A1b.conjSub e A ⊔ A1b.conjSub e B := by
  unfold A1b.conjSub
  exact Subgroup.map_sup _ _ _

theorem sec_conjSub_iSup {ι : Sort*} (e : G) (F : ι → Subgroup G) :
    A1b.conjSub e (⨆ i, F i) = ⨆ i, A1b.conjSub e (F i) := by
  unfold A1b.conjSub
  exact Subgroup.map_iSup _ _

theorem sec_le_normalizer_of_conj {A H : Subgroup G}
    (hA : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) : A ≤ Subgroup.normalizer (H : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hA a ha x hx, fun hx => ?_⟩
  have h := hA a⁻¹ (A.inv_mem ha) _ hx
  simpa [mul_assoc] using h

theorem sec_conj_mem_of_normal_subgroupOf {N S : Subgroup G} (hN : (N.subgroupOf S).Normal)
    {s : G} (hs : s ∈ S) {n : G} (hn : n ∈ N) (hnS : n ∈ S) : s * n * s⁻¹ ∈ N := by
  have h := hN.conj_mem ⟨n, hnS⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨s, hs⟩
  have h' := Subgroup.mem_subgroupOf.mp h
  simpa using h'

theorem sec_iSup_conj_mem {ι : Sort*} {F : ι → Subgroup G} {X : Subgroup G}
    (hF : ∀ s ∈ X, ∀ i, ∀ x ∈ F i, s * x * s⁻¹ ∈ F i) {s : G} (hs : s ∈ X) {x : G}
    (hx : x ∈ ⨆ i, F i) : s * x * s⁻¹ ∈ ⨆ i, F i := by
  refine Subgroup.iSup_induction F (C := fun y => s * y * s⁻¹ ∈ ⨆ i, F i) hx ?_ ?_ ?_
  · intro i y hy
    exact Subgroup.mem_iSup_of_mem i (hF s hs i y hy)
  · show s * 1 * s⁻¹ ∈ ⨆ i, F i
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro a b ha hb
    show s * (a * b) * s⁻¹ ∈ ⨆ i, F i
    have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb

theorem sec_simple_sup {L P D YM Y S N : Subgroup G}
    (hY : Y = D ⊓ YM) (hS' : S = P ⊔ Y) (hPD : P ≤ D) (hPL : P ≤ L) (hYL : YM ≤ L)
    (hLkey : L ≤ P ⊔ YM) (hYn : ∀ l ∈ L, ∀ y ∈ YM, l * y * l⁻¹ ∈ YM)
    (hsimpleL : ∀ N : Subgroup G, YM ≤ N → N ≤ L → (N.subgroupOf L).Normal → N = YM ∨ N = L)
    (hYN : Y ≤ N) (hNS : N ≤ S) (hnorm : (N.subgroupOf S).Normal) : N = Y ∨ N = S := by
  subst hS'
  have hYD : Y ≤ D := by rw [hY]; exact inf_le_left
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) := by
    refine sec_le_normalizer_of_conj fun p hp y hy => ?_
    rw [hY] at hy ⊢
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨D.mul_mem (D.mul_mem (hPD hp) hy.1) (D.inv_mem (hPD hp)), hYn p (hPL hp) y hy.2⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = (N ⊓ P) ⊔ YM := ⟨_, rfl⟩
  have hNP_YM : N ⊓ P ≤ Subgroup.normalizer (YM : Set G) := fun n hn =>
    sec_normalizer_of_conj_mem hYn (hPL (Subgroup.mem_inf.mp hn).2)
  have hWP : ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W := by
    intro p hp w hw
    rw [hW] at hw ⊢
    rw [sup_comm] at hw
    obtain ⟨y, hy, n, hn, rfl⟩ := E111R.exists_mul_of_mem_sup hNP_YM hw
    have hn' := Subgroup.mem_inf.mp hn
    have e : p * (y * n) * p⁻¹ = (p * y * p⁻¹) * (p * n * p⁻¹) := by group
    rw [e, sup_comm]
    have h1 : p * y * p⁻¹ ∈ YM := hYn p (hPL hp) y hy
    have h2 : p * n * p⁻¹ ∈ N ⊓ P :=
      Subgroup.mem_inf.mpr ⟨sec_conj_mem_of_normal_subgroupOf hnorm (Subgroup.mem_sup_left hp)
        hn'.1 (hNS hn'.1), P.mul_mem (P.mul_mem hp hn'.2) (P.inv_mem hp)⟩
    exact Subgroup.mul_mem_sup h1 h2
  have hWY : ∀ y ∈ YM, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    rw [hW] at hw ⊢
    rw [sup_comm] at hw
    obtain ⟨y', hy', n, hn, rfl⟩ := E111R.exists_mul_of_mem_sup hNP_YM hw
    have hn' := Subgroup.mem_inf.mp hn
    have hnL : n⁻¹ ∈ L := L.inv_mem (hPL hn'.2)
    have hz : (n⁻¹ * y * n⁻¹⁻¹) * y⁻¹ ∈ YM := YM.mul_mem (hYn n⁻¹ hnL y hy) (YM.inv_mem hy)
    have e : y * (y' * n) * y⁻¹ = (y * y' * y⁻¹) * (n * ((n⁻¹ * y * n⁻¹⁻¹) * y⁻¹)) := by
      group
    rw [e]
    have h1 : y * y' * y⁻¹ ∈ YM := YM.mul_mem (YM.mul_mem hy hy') (YM.inv_mem hy)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mul_mem_sup hn hz)
  have hYW : YM ≤ W := by rw [hW]; exact le_sup_right
  have hWL : W ≤ L := by rw [hW]; exact sup_le (inf_le_right.trans hPL) hYL
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    hLkey.trans (sup_le (sec_le_normalizer_of_conj hWP) (sec_le_normalizer_of_conj hWY))
  have hWnorm : (W.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr hLW
  rcases hsimpleL W hYW hWL hWnorm with hW1 | hW2
  · left
    refine le_antisymm (fun x hx => ?_) hYN
    obtain ⟨y, hy, p, hp, rfl⟩ := E111R.exists_mul_of_mem_sup hPY
      (by rw [sup_comm]; exact hNS hx)
    have hpN : p ∈ N := by
      have := N.mul_mem (N.inv_mem (hYN hy)) hx
      simpa using this
    have hpYM : p ∈ YM := by
      have h : p ∈ W := by
        rw [hW]
        exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hpN, hp⟩)
      rw [hW1] at h
      exact h
    have hpY : p ∈ Y := by rw [hY]; exact Subgroup.mem_inf.mpr ⟨hPD hp, hpYM⟩
    exact Y.mul_mem hy hpY
  · right
    refine le_antisymm hNS ?_
    refine sup_le ?_ hYN
    intro p hp
    have hpW : p ∈ W := by rw [hW2]; exact hPL hp
    rw [hW, sup_comm] at hpW
    obtain ⟨y, hy, n, hn, rfl⟩ := E111R.exists_mul_of_mem_sup hNP_YM hpW
    have hn' := Subgroup.mem_inf.mp hn
    have hyP : y ∈ P := by
      have := P.mul_mem hp (P.inv_mem hn'.2)
      simpa using this
    have hyY : y ∈ Y := by rw [hY]; exact Subgroup.mem_inf.mpr ⟨hPD hyP, hy⟩
    exact N.mul_mem (hYN hyY) hn'.1

theorem jdata_of_section {T M XM YM E J : Subgroup G} {ℒ : Set (Subgroup G)}
    (hS : SecData M XM YM ℒ) (hEM : E ≤ M) (hXJ : XM ≤ J) (hSylX : IsSylowIn 2 (T ⊓ XM) XM)
    {L₁ : Subgroup G} (hL₁ : L₁ ∈ ℒ) :
    ∃ (D Y D₁ : Subgroup G) (𝒟 : Set (Subgroup G)),
      JData E J D Y 𝒟 ∧ IsSylowIn 2 (T ⊓ D) D ∧ D₁ = perfectCore L₁ ∧ D₁ ≤ D ∧ D ≤ XM ∧
        Y = D ⊓ YM ∧ D₁ ⊔ Y ∈ 𝒟 ∧ (∀ L ∈ ℒ, ∃ m ∈ M, L ≤ conjSub m D₁ ⊔ YM) := by
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Subgroup G, D₁ = perfectCore L₁ := ⟨_, rfl⟩
  have hD₁L : D₁ ≤ L₁ := by rw [hD₁]; exact perfectCore_le L₁
  have hD₁perf : ⁅D₁, D₁⁆ = D₁ := by rw [hD₁]; exact perfectCore_perfect L₁
  have hkey : L₁ ≤ D₁ ⊔ YM := by rw [hD₁]; exact key_le_perfectCore_sup hS hL₁
  have hL₁XM : L₁ ≤ XM := hS.SM.le_D L₁ hL₁
  have hYL : YM ≤ L₁ := hS.SM.Y_le L₁ hL₁
  have hLe : ∀ e ∈ E, A1b.conjSub e L₁ ∈ ℒ := fun e he => hS.SM.conj L₁ hL₁ e (hEM he)
  have hYe : ∀ e ∈ E, A1b.conjSub e YM = YM := fun e he =>
    E111R.conjSub_eq_of_mem_normalizer (hS.M_Y (hEM he))
  have hLeXM : ∀ e ∈ E, A1b.conjSub e L₁ ≤ XM := fun e he => hS.SM.le_D _ (hLe e he)
  have hDe : ∀ e ∈ E, A1b.conjSub e D₁ = perfectCore (A1b.conjSub e L₁) := by
    intro e _
    rw [hD₁]
    exact map_perfectCore (MulAut.conj e : G →* G) L₁
  have hDeperf : ∀ e : G, ⁅A1b.conjSub e D₁, A1b.conjSub e D₁⁆ = A1b.conjSub e D₁ := by
    intro e
    unfold A1b.conjSub
    rw [← Subgroup.map_commutator, hD₁perf]
  have hLeKey : ∀ e ∈ E, A1b.conjSub e L₁ ≤ A1b.conjSub e D₁ ⊔ YM := by
    intro e he
    have h := A1b.conjSub_mono e hkey
    rw [sec_conjSub_sup, hYe e he] at h
    exact h
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = ⨆ e : E, A1b.conjSub (e : G) D₁ := ⟨_, rfl⟩
  have hDgen : ∀ e ∈ E, A1b.conjSub e D₁ ≤ D := by
    intro e he
    rw [hD]
    exact le_iSup (fun e : E => A1b.conjSub (e : G) D₁) ⟨e, he⟩
  have hD₁D : D₁ ≤ D := by
    have h := hDgen 1 E.one_mem
    rwa [A1b.conjSub_one] at h
  have hDXM : D ≤ XM := by
    rw [hD]
    refine iSup_le fun e => ?_
    exact (A1b.conjSub_mono _ hD₁L).trans (hLeXM _ e.2)
  have hDJ : D ≤ J := hDXM.trans hXJ
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (E111R.commutator_le_self D) ?_
    calc D = ⨆ e : E, A1b.conjSub (e : G) D₁ := hD
      _ ≤ ⁅D, D⁆ := by
        refine iSup_le fun e => ?_
        calc A1b.conjSub (e : G) D₁
            = ⁅A1b.conjSub (e : G) D₁, A1b.conjSub (e : G) D₁⁆ := (hDeperf _).symm
          _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono (hDgen _ e.2) (hDgen _ e.2)
  have hDnorm : (D.subgroupOf XM).Normal := by
    refine normal_subgroupOf_of_conj hDXM fun s hs n hn => ?_
    have hF : ∀ s ∈ XM, ∀ e : E, ∀ x ∈ A1b.conjSub (e : G) D₁,
        s * x * s⁻¹ ∈ A1b.conjSub (e : G) D₁ := by
      intro s hs e x hx
      have h1 : s ∈ Subgroup.normalizer ((A1b.conjSub (e : G) L₁ : Subgroup G) : Set G) :=
        hS.SM.D_le_normalizer (hLe _ e.2) hs
      have h2 := normalizer_le_normalizer_perfectCore _ h1
      rw [← hDe _ e.2] at h2
      exact (Subgroup.mem_normalizer_iff.mp h2 x).mp hx
    rw [hD] at hn ⊢
    exact sec_iSup_conj_mem (F := fun e : E => A1b.conjSub (e : G) D₁) hF hs hn
  have hSylD : IsSylowIn 2 (T ⊓ D) D := by
    have h := hSylX.inf_normal hDXM hDnorm
    rwa [inf_assoc, inf_eq_right.mpr hDXM] at h
  have hDle : ∀ e ∈ E, A1b.conjSub e D ≤ D := by
    intro e he
    have h : A1b.conjSub e D = ⨆ i : E, A1b.conjSub e (A1b.conjSub (i : G) D₁) := by
      rw [hD, sec_conjSub_iSup]
    rw [h]
    refine iSup_le fun i => ?_
    rw [← A1b.conjSub_mul]
    exact hDgen _ (E.mul_mem he i.2)
  have hDE : ∀ e ∈ E, A1b.conjSub e D = D := by
    intro e he
    refine le_antisymm (hDle e he) ?_
    have h1 := A1b.conjSub_mono e (hDle e⁻¹ (E.inv_mem he))
    rwa [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at h1
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = D ⊓ YM := ⟨_, rfl⟩
  have hYD : Y ≤ D := by rw [hY]; exact inf_le_left
  have hYYM : Y ≤ YM := by rw [hY]; exact inf_le_right
  have hYsolv : Group.IsSolvable ↥Y := by
    haveI := hS.Ysolv
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYYM)
      (Subgroup.inclusion_injective hYYM)
  have hYnormD : (Y.subgroupOf D).Normal := by
    refine normal_subgroupOf_of_conj hYD fun s hs n hn => ?_
    rw [hY] at hn ⊢
    rw [Subgroup.mem_inf] at hn ⊢
    exact ⟨D.mul_mem (D.mul_mem hs hn.1) (D.inv_mem hs),
      (Subgroup.mem_normalizer_iff.mp (hS.X_Y (hDXM hs)) n).mp hn.2⟩
  have hYE : ∀ e ∈ E, A1b.conjSub e Y = Y := by
    intro e he
    ext x
    have hmemD : ∀ z, z ∈ D ↔ e⁻¹ * z * e ∈ D := fun z => by
      have h : z ∈ A1b.conjSub e D ↔ e⁻¹ * z * e ∈ D := A1b.mem_conjSub_iff
      rw [hDE e he] at h
      exact h
    have hmemYM : ∀ z, z ∈ YM ↔ e⁻¹ * z * e ∈ YM := fun z => by
      have h : z ∈ A1b.conjSub e YM ↔ e⁻¹ * z * e ∈ YM := A1b.mem_conjSub_iff
      rw [hYe e he] at h
      exact h
    rw [A1b.mem_conjSub_iff, hY, Subgroup.mem_inf, Subgroup.mem_inf, ← hmemD x, ← hmemYM x]
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : Set (Subgroup G),
      ∀ S, S ∈ 𝒟 ↔ ∃ e ∈ E, A1b.conjSub e (D₁ ⊔ Y) = S :=
    ⟨(fun e : G => A1b.conjSub e (D₁ ⊔ Y)) '' (E : Set G), fun S => Iff.rfl⟩
  have hD₁Y : D₁ ⊔ Y ∈ 𝒟 := (h𝒟 _).mpr ⟨1, E.one_mem, A1b.conjSub_one _⟩
  have hSdef : ∀ e ∈ E, A1b.conjSub e (D₁ ⊔ Y) = A1b.conjSub e D₁ ⊔ Y := fun e he => by
    rw [sec_conjSub_sup, hYE e he]
  have hSmem : ∀ e ∈ E, A1b.conjSub e (D₁ ⊔ Y) ∈ 𝒟 := fun e he => (h𝒟 _).mpr ⟨e, he, rfl⟩
  have hSD : ∀ e ∈ E, A1b.conjSub e (D₁ ⊔ Y) ≤ D := fun e he =>
    (A1b.conjSub_mono e (sup_le hD₁D hYD)).trans (le_of_eq (hDE e he))
  have hSM : SemisimpleMod E D Y 𝒟 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro S hS'
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
      calc Y = A1b.conjSub e Y := (hYE e he).symm
        _ ≤ A1b.conjSub e (D₁ ⊔ Y) := A1b.conjSub_mono e le_sup_right
    · intro S hS'
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
      exact hSD e he
    · intro S hS' N hYN hNS hnorm
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
      exact sec_simple_sup hY (hSdef e he) (hDgen e he) (A1b.conjSub_mono e hD₁L)
        (hS.SM.Y_le _ (hLe e he)) (hLeKey e he)
        (fun l hl y hy => (Subgroup.mem_normalizer_iff.mp (hS.X_Y (hLeXM e he hl)) y).mp hy)
        (hS.SM.simple _ (hLe e he)) hYN hNS hnorm
    · intro S hS' hcon
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
      have h1 : A1b.conjSub e D₁ ≤ A1b.conjSub e (D₁ ⊔ Y) := A1b.conjSub_mono e le_sup_left
      have h2 : ⁅A1b.conjSub e D₁, A1b.conjSub e D₁⁆ ≤ Y :=
        (Subgroup.commutator_mono h1 h1).trans hcon
      rw [hDeperf e] at h2
      have hP : A1b.conjSub e D₁ ≤ YM := h2.trans hYYM
      have hL : A1b.conjSub e L₁ ≤ YM := (hLeKey e he).trans (sup_le hP le_rfl)
      exact hS.SM.nonab _ (hLe e he)
        ((Subgroup.commutator_mono hL hL).trans (E111R.commutator_le_self YM))
    · intro S hS1 S' hS2 hne
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS1
      obtain ⟨e', he', rfl⟩ := (h𝒟 _).mp hS2
      have hLne : A1b.conjSub e L₁ ≠ A1b.conjSub e' L₁ := by
        intro hLeq
        apply hne
        have hDeq : A1b.conjSub e D₁ = A1b.conjSub e' D₁ := by
          rw [hDe e he, hDe e' he', hLeq]
        rw [hSdef e he, hSdef e' he', hDeq]
      have hcomm := hS.SM.comm _ (hLe e he) _ (hLe e' he') hLne
      have hSL : A1b.conjSub e (D₁ ⊔ Y) ≤ A1b.conjSub e L₁ :=
        A1b.conjSub_mono e (sup_le hD₁L (hYYM.trans hYL))
      have hSL' : A1b.conjSub e' (D₁ ⊔ Y) ≤ A1b.conjSub e' L₁ :=
        A1b.conjSub_mono e' (sup_le hD₁L (hYYM.trans hYL))
      have h1 : ⁅A1b.conjSub e (D₁ ⊔ Y), A1b.conjSub e' (D₁ ⊔ Y)⁆ ≤ YM :=
        (Subgroup.commutator_mono hSL hSL').trans hcomm
      have h2 : ⁅A1b.conjSub e (D₁ ⊔ Y), A1b.conjSub e' (D₁ ⊔ Y)⁆ ≤ D :=
        (Subgroup.commutator_mono (hSD e he) (hSD e' he')).trans (le_of_eq hDperf)
      have h3 : ⁅A1b.conjSub e (D₁ ⊔ Y), A1b.conjSub e' (D₁ ⊔ Y)⁆ ≤ D ⊓ YM := le_inf h2 h1
      rw [← hY] at h3
      exact h3
    · apply le_antisymm
      · exact iSup₂_le fun S hS' => by
          obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
          exact hSD e he
      · rw [hD]
        refine iSup_le fun e => ?_
        exact le_iSup₂_of_le (A1b.conjSub (e : G) (D₁ ⊔ Y)) (hSmem _ e.2)
          (A1b.conjSub_mono _ le_sup_left)
    · intro S hS' t ht
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS'
      exact (h𝒟 _).mpr ⟨t * e, E.mul_mem ht he, A1b.conjSub_mul t e _⟩
    · intro S hS1 S' hS2
      obtain ⟨e, he, rfl⟩ := (h𝒟 _).mp hS1
      obtain ⟨e', he', rfl⟩ := (h𝒟 _).mp hS2
      refine ⟨e' * e⁻¹, E.mul_mem he' (E.inv_mem he), ?_⟩
      rw [← A1b.conjSub_mul, inv_mul_cancel_right]
  have hJD : JData E J D Y 𝒟 :=
    ⟨hSM, ⟨D₁ ⊔ Y, hD₁Y⟩, hDJ, hDperf, hYsolv, hYnormD, hYE⟩
  refine ⟨D, Y, D₁, 𝒟, hJD, hSylD, hD₁, hD₁D, hDXM, hY, hD₁Y, ?_⟩
  intro L hL
  obtain ⟨m, hm, hmL⟩ := hS.SM.trans L₁ hL₁ L hL
  refine ⟨m, hm, ?_⟩
  rw [← hmL]
  have hYm : A1b.conjSub m YM = YM := E111R.conjSub_eq_of_mem_normalizer (hS.M_Y hm)
  have h := A1b.conjSub_mono m hkey
  rw [sec_conjSub_sup, hYm] at h
  exact h

end CFSG.Quasithin.RonanE111
