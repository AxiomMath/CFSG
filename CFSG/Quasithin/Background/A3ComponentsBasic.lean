module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

namespace A3

theorem subnormal_le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem subnormal_trans {H M K : Subgroup G} (h₁ : IsSubnormal H M) (h₂ : IsSubnormal M K) :
    IsSubnormal H K :=
  h₁.trans h₂

theorem subnormal_of_normal {H K : Subgroup G} (hle : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    IsSubnormal H K :=
  IsSubnormal.step hle hN (IsSubnormal.refl K)

theorem subnormal_inf_right {H K : Subgroup G} (h : IsSubnormal H K) :
    ∀ {L : Subgroup G}, L ≤ K → IsSubnormal (H ⊓ L) L :=
  fun hL => h.inf_of_le hL

theorem subnormal_of_le_of_le {H K L : Subgroup G} (h : IsSubnormal H K) (hHL : H ≤ L)
    (hLK : L ≤ K) : IsSubnormal H L := by
  simpa [inf_eq_left.mpr hHL] using subnormal_inf_right h hLK

theorem subnormal_map {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : IsSubnormal H K) : IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem subnormal_comap {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G'}
    (h : IsSubnormal H K) : IsSubnormal (H.comap f) (K.comap f) :=
  h.comap f

theorem subnormal_exists_normal_of_lt {H K : Subgroup G} (h : IsSubnormal H K) (hlt : H < K) :
    ∃ P : Subgroup G, P < K ∧ (P.subgroupOf K).Normal ∧ H ≤ P := by
  induction h with
  | refl => exact absurd hlt (lt_irrefl _)
  | @step H M K hle hN hMK ih =>
    rcases eq_or_lt_of_le (subnormal_le hMK) with hMeq | hMlt
    · subst hMeq
      exact ⟨H, hlt, hN, le_rfl⟩
    · obtain ⟨P, hPK, hPn, hMP⟩ := ih hMlt
      exact ⟨P, hPK, hPn, hle.trans hMP⟩

end A3

@[expose] def derivedSeriesOf (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅derivedSeriesOf H n, derivedSeriesOf H n⁆

@[expose] def perfectCore (H : Subgroup G) : Subgroup G := ⨅ n, derivedSeriesOf H n

theorem derivedSeriesOf_zero (H : Subgroup G) : derivedSeriesOf H 0 = H := rfl

theorem derivedSeriesOf_succ (H : Subgroup G) (n : ℕ) :
    derivedSeriesOf H (n + 1) = ⁅derivedSeriesOf H n, derivedSeriesOf H n⁆ := rfl

theorem A3.commutator_self_le (A : Subgroup G) : ⁅A, A⁆ ≤ A :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    simpa [commutatorElement_def] using
      A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem derivedSeriesOf_antitone (H : Subgroup G) : Antitone (derivedSeriesOf H) :=
  antitone_nat_of_succ_le fun _ => A3.commutator_self_le _

theorem derivedSeriesOf_le (H : Subgroup G) (n : ℕ) : derivedSeriesOf H n ≤ H :=
  derivedSeriesOf_antitone H (Nat.zero_le n)

theorem perfectCore_le (H : Subgroup G) : perfectCore H ≤ H := iInf_le _ 0

theorem perfectCore_le_derivedSeriesOf (H : Subgroup G) (n : ℕ) :
    perfectCore H ≤ derivedSeriesOf H n := iInf_le _ n

theorem derivedSeriesOf_mono {H K : Subgroup G} (h : H ≤ K) (n : ℕ) :
    derivedSeriesOf H n ≤ derivedSeriesOf K n := by
  induction n with
  | zero => exact h
  | succ n ih => exact Subgroup.commutator_mono ih ih

theorem perfectCore_mono {H K : Subgroup G} (h : H ≤ K) : perfectCore H ≤ perfectCore K :=
  iInf_mono fun n => derivedSeriesOf_mono h n

theorem map_derivedSeriesOf {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G) (n : ℕ) :
    (derivedSeriesOf H n).map f = derivedSeriesOf (H.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [derivedSeriesOf_succ, Subgroup.map_commutator, ih]; rfl

theorem derivedSeriesOf_eq_map_derivedSeries (H : Subgroup G) (n : ℕ) :
    derivedSeriesOf H n = (derivedSeries H n).map H.subtype := by
  induction n with
  | zero => rw [derivedSeriesOf_zero, derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeriesOf_succ, ih, derivedSeries_succ, Subgroup.map_commutator]

theorem le_derivedSeriesOf_of_perfect {K H : Subgroup G} (hKH : K ≤ H) (hK : ⁅K, K⁆ = K)
    (n : ℕ) : K ≤ derivedSeriesOf H n := by
  induction n with
  | zero => exact hKH
  | succ n ih => rw [derivedSeriesOf_succ, ← hK]; exact Subgroup.commutator_mono ih ih

theorem le_perfectCore_of_perfect {K H : Subgroup G} (hKH : K ≤ H) (hK : ⁅K, K⁆ = K) :
    K ≤ perfectCore H :=
  le_iInf fun n => le_derivedSeriesOf_of_perfect hKH hK n

theorem perfectCore_eq_self_of_perfect {H : Subgroup G} (hH : ⁅H, H⁆ = H) :
    perfectCore H = H :=
  le_antisymm (perfectCore_le H) (le_perfectCore_of_perfect le_rfl hH)

theorem A3.commutator_iSup_eq_of_perfect {ι : Type*} (K : ι → Subgroup G)
    (hK : ∀ i, ⁅K i, K i⁆ = K i) : ⁅⨆ i, K i, ⨆ i, K i⁆ = ⨆ i, K i := by
  refine le_antisymm (A3.commutator_self_le _) (iSup_le fun i => ?_)
  calc K i = ⁅K i, K i⁆ := (hK i).symm
    _ ≤ ⁅⨆ i, K i, ⨆ i, K i⁆ :=
      Subgroup.commutator_mono (le_iSup K i) (le_iSup K i)

theorem exists_perfectCore_eq [Finite G] (H : Subgroup G) :
    ∃ n, ∀ m, n ≤ m → perfectCore H = derivedSeriesOf H m := by
  obtain ⟨x, hx⟩ := (Set.toFinite (Set.range (derivedSeriesOf H))).exists_minimal
    ⟨derivedSeriesOf H 0, ⟨0, rfl⟩⟩
  obtain ⟨n, rfl⟩ := hx.prop
  have hstab : ∀ m, n ≤ m → derivedSeriesOf H m = derivedSeriesOf H n := fun m hm =>
    hx.eq_of_le ⟨m, rfl⟩ (derivedSeriesOf_antitone H hm)
  have hcore : perfectCore H = derivedSeriesOf H n := by
    refine le_antisymm (iInf_le _ n) (le_iInf fun m => ?_)
    rcases le_total n m with hm | hm
    · exact (hstab m hm).ge
    · exact derivedSeriesOf_antitone H hm
  exact ⟨n, fun m hm => by rw [hcore, hstab m hm]⟩

theorem perfectCore_perfect [Finite G] (H : Subgroup G) :
    ⁅perfectCore H, perfectCore H⁆ = perfectCore H := by
  obtain ⟨n, hn⟩ := exists_perfectCore_eq H
  have h1 := hn n le_rfl
  have h2 := hn (n + 1) (Nat.le_succ n)
  rw [derivedSeriesOf_succ, ← h1] at h2
  exact h2.symm

theorem perfectCore_eq_self_iff [Finite G] (H : Subgroup G) : perfectCore H = H ↔ ⁅H, H⁆ = H :=
  ⟨fun h => by simpa [h] using perfectCore_perfect H, perfectCore_eq_self_of_perfect⟩

theorem map_perfectCore [Finite G] {G' : Type*} [Group G'] [Finite G'] (f : G →* G')
    (H : Subgroup G) : (perfectCore H).map f = perfectCore (H.map f) := by
  obtain ⟨n₁, h₁⟩ := exists_perfectCore_eq H
  obtain ⟨n₂, h₂⟩ := exists_perfectCore_eq (H.map f)
  have e₁ := h₁ (max n₁ n₂) (le_max_left _ _)
  have e₂ := h₂ (max n₁ n₂) (le_max_right _ _)
  rw [e₁, e₂, map_derivedSeriesOf]

theorem map_conj_derivedSeriesOf {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (n : ℕ) : (derivedSeriesOf H n).map (MulAut.conj g : G →* G) = derivedSeriesOf H n := by
  rw [map_derivedSeriesOf, Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]

theorem normalizer_le_normalizer_perfectCore (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (perfectCore H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [perfectCore, Subgroup.map_iInf _ (MulAut.conj g).injective]
  exact iInf_congr fun n => map_conj_derivedSeriesOf hg n

theorem perfectCore_normal (H : Subgroup G) : ((perfectCore H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le H)).mpr
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H))

theorem A3.subnormal_perfectCore {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (perfectCore H) K :=
  A3.subnormal_trans (A3.subnormal_of_normal (perfectCore_le H) (perfectCore_normal H)) h

theorem isSolvable_iff_exists_derivedSeriesOf_eq_bot (H : Subgroup G) :
    Group.IsSolvable H ↔ ∃ n, derivedSeriesOf H n = ⊥ := by
  rw [Group.isSolvable_def]
  refine exists_congr fun n => ?_
  rw [derivedSeriesOf_eq_map_derivedSeries, ← Subgroup.map_bot H.subtype]
  exact (Subgroup.map_injective H.subtype_injective).eq_iff.symm

theorem isSolvable_iff_perfectCore_eq_bot [Finite G] (H : Subgroup G) :
    Group.IsSolvable H ↔ perfectCore H = ⊥ := by
  rw [isSolvable_iff_exists_derivedSeriesOf_eq_bot]
  constructor
  · rintro ⟨n, hn⟩
    exact le_bot_iff.mp ((perfectCore_le_derivedSeriesOf H n).trans hn.le)
  · intro h
    obtain ⟨n, hn⟩ := exists_perfectCore_eq H
    exact ⟨n, by rw [← hn n le_rfl, h]⟩

theorem A3.isSolvable_sup_of_le_normalizer {M N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (M : Set G)) [Group.IsSolvable M] [Group.IsSolvable N] :
    Group.IsSolvable ↥(M ⊔ N) := by
  have hML : M ≤ M ⊔ N := le_sup_left
  have hNL : N ≤ M ⊔ N := le_sup_right
  have hLnorm : M ⊔ N ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hN
  have hnormal : (M.subgroupOf (M ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr hLnorm
  have hMsolv : Group.IsSolvable ↥(M.subgroupOf (M ⊔ N)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hML).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hML).injective
  let f : ↥N →* ↥(M ⊔ N) ⧸ M.subgroupOf (M ⊔ N) :=
    (QuotientGroup.mk' (M.subgroupOf (M ⊔ N))).comp (Subgroup.inclusion hNL)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf (M ⊔ N)) y
    have hx' : x ∈ (↑(M ⊔ N) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M N hN] at hx'
    obtain ⟨m, hm, n, hn, rfl⟩ := hx'
    refine ⟨⟨n, hn⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hn' : n ∈ Subgroup.normalizer (M : Set G) := hN hn
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn') m).mp hm
    simpa [mul_assoc] using this
  have : Group.IsSolvable (↥(M ⊔ N) ⧸ M.subgroupOf (M ⊔ N)) :=
    Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (M.subgroupOf (M ⊔ N))

@[expose] def solvRad (H : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Group.IsSolvable N}

theorem solvRad_le (H : Subgroup G) : solvRad H ≤ H := sSup_le fun _ hN => hN.1

theorem le_solvRad {H N : Subgroup G} (hNH : N ≤ H) (hn : (N.subgroupOf H).Normal)
    (hs : Group.IsSolvable N) : N ≤ solvRad H :=
  le_sSup ⟨hNH, hn, hs⟩

theorem conj_mem_solvRad {H : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hx : x ∈ solvRad H) : g * x * g⁻¹ ∈ solvRad H := by
  have key : solvRad H ≤ (solvRad H).comap (MulAut.conj g : G →* G) := by
    refine sSup_le fun N hN y hy => ?_
    obtain ⟨hNH, hNn, hNs⟩ := hN
    have hgH : ∀ z ∈ H, g * z * g⁻¹ ∈ H := fun z hz => (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    have hgH' : ∀ z ∈ H, g⁻¹ * z * g ∈ H := fun z hz => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp hz
      simpa using this
    have hN'H : N.map (MulAut.conj g : G →* G) ≤ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact hgH z (hNH hz)
    have hN'n : ((N.map (MulAut.conj g : G →* G)).subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hN'H]
      rintro _ h ⟨z, hz, rfl⟩ hh
      have hzn : (g⁻¹ * h * g) * z * (g⁻¹ * h * g)⁻¹ ∈ N :=
        (Subgroup.normal_subgroupOf_iff hNH).mp hNn z (g⁻¹ * h * g) hz (hgH' h hh)
      refine ⟨_, hzn, ?_⟩
      show g * ((g⁻¹ * h * g) * z * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * z * g⁻¹) * h⁻¹
      group
    have : Group.IsSolvable ↥N := hNs
    have hN's : Group.IsSolvable ↥(N.map (MulAut.conj g : G →* G)) :=
      Group.isSolvable_of_surjective (f := (N.equivMapOfInjective (MulAut.conj g : G →* G)
        (MulAut.conj g).injective).toMonoidHom) (N.equivMapOfInjective _ _).surjective
    exact le_solvRad hN'H hN'n hN's ⟨y, hy, rfl⟩
  exact key hx

theorem normalizer_le_normalizer_solvRad (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (solvRad H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · exact (conj_mem_solvRad hg hx)
  · have := conj_mem_solvRad (Subgroup.inv_mem _ hg) hx
    simpa [mul_assoc] using this

theorem solvRad_normal (H : Subgroup G) : ((solvRad H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (solvRad_le H)).mpr
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H))

instance solvRad_subgroupOf_normal (H : Subgroup G) : ((solvRad H).subgroupOf H).Normal :=
  solvRad_normal H

theorem solvRad_isSolvable [Finite G] (H : Subgroup G) : Group.IsSolvable ↥(solvRad H) := by
  classical
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup G => N ≤ H ∧ (N.subgroupOf H).Normal ∧ Group.IsSolvable N)
    (a := ⊥)
    ⟨bot_le, by rw [Subgroup.bot_subgroupOf]; exact Subgroup.normal_bot, inferInstance⟩
  have hge : ∀ N ∈ {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Group.IsSolvable N},
      N ≤ M := by
    rintro N ⟨hNH, hNn, hNs⟩
    obtain ⟨hMH, hMn, hMs⟩ := hM.1
    have := hMs
    have := hNs
    have hNnorm : N ≤ Subgroup.normalizer (M : Set G) :=
      hNH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMH).mp hMn)
    have hsup : M ⊔ N ≤ H ∧ ((M ⊔ N).subgroupOf H).Normal ∧ Group.IsSolvable ↥(M ⊔ N) := by
      refine ⟨sup_le hMH hNH, ?_, A3.isSolvable_sup_of_le_normalizer hNnorm⟩
      rw [Subgroup.subgroupOf_sup hMH hNH]
      have := hMn
      have := hNn
      infer_instance
    exact le_sup_right.trans (hM.2 hsup le_sup_left)
  have heq : solvRad H = M := le_antisymm (sSup_le hge) (le_sSup hM.1)
  rw [heq]
  exact hM.1.2.2

theorem solvRad_le_solvRad_of_subnormal [Finite G] {H K : Subgroup G} (h : IsSubnormal H K) :
    solvRad H ≤ solvRad K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine le_solvRad ((solvRad_le H).trans hle) ?_ (solvRad_isSolvable H)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((solvRad_le H).trans hle)]
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN).trans
      (normalizer_le_normalizer_solvRad H)

theorem le_solvRad_of_subnormal [Finite G] {N K : Subgroup G} (hN : IsSubnormal N K)
    (hs : Group.IsSolvable N) : N ≤ solvRad K := by
  refine (le_solvRad le_rfl ?_ hs).trans (solvRad_le_solvRad_of_subnormal hN)
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.normal_top

theorem solvRad_eq_self_iff [Finite G] (H : Subgroup G) :
    solvRad H = H ↔ Group.IsSolvable H := by
  constructor
  · intro h
    have := solvRad_isSolvable H
    rw [h] at this
    exact this
  · intro hs
    exact le_antisymm (solvRad_le H) (le_solvRad le_rfl (by
      rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hs)

theorem A3.eq_sup_inf_of_le_sup {L N P : Subgroup G} (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (hLP : L ≤ P) (hP : P ≤ L ⊔ N) : P = L ⊔ (P ⊓ N) := by
  refine le_antisymm ?_ (sup_le hLP inf_le_left)
  intro x hx
  have hx' : x ∈ (↑(L ⊔ N) : Set G) := hP hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L N hLN] at hx'
  obtain ⟨l, hl, n, hn, rfl⟩ := hx'
  have hn' : n ∈ P := by
    have := P.mul_mem (P.inv_mem (hLP hl)) hx
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hn', hn⟩)

theorem perfectCore_le_of_sup_solvable {A B Y : Subgroup G} (hAY : A ≤ Y)
    (hA : (A.subgroupOf Y).Normal) (hY : Y = A ⊔ B) (hB : Group.IsSolvable B) :
    perfectCore Y ≤ A := by
  have hBY : B ≤ Y := hY ▸ le_sup_right
  have hBnorm : B ≤ Subgroup.normalizer (A : Set G) :=
    hBY.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAY).mp hA)
  let f : ↥B →* ↥Y ⧸ A.subgroupOf Y :=
    (QuotientGroup.mk' (A.subgroupOf Y)).comp (Subgroup.inclusion hBY)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf Y) y
    have hx' : x ∈ (↑(A ⊔ B) : Set G) := hY ▸ hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBnorm] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hb' : b ∈ Subgroup.normalizer (A : Set G) := hBnorm hb
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb') a).mp ha
    simpa [mul_assoc] using this
  have : Group.IsSolvable ↥B := hB
  have : Group.IsSolvable (↥Y ⧸ A.subgroupOf Y) := Group.isSolvable_of_surjective hf
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp this
  have h1 : (derivedSeries (↥Y) n).map (QuotientGroup.mk' (A.subgroupOf Y)) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _) n, hn]
  have h2 : derivedSeries (↥Y) n ≤ A.subgroupOf Y := by
    rw [← QuotientGroup.ker_mk' (A.subgroupOf Y), ← Subgroup.map_eq_bot_iff]
    exact h1
  have h3 := Subgroup.map_mono (f := Y.subtype) h2
  rw [← derivedSeriesOf_eq_map_derivedSeries, Subgroup.map_subgroupOf_eq_of_le hAY] at h3
  exact (perfectCore_le_derivedSeriesOf Y n).trans h3

end CFSG.Quasithin
