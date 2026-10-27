module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RTuple

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section CdSound

variable {τ : Tag} {S : TcrSys}

theorem tcrPows_rv (φ : AddMonoid.End (Fin τ.rank → ℤ)) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i)) :
    ∀ e ≤ 24, ∀ i < S.tcrN, ((tcrPermPows S perm)[e]!)[i]! < S.tcrN ∧
      tcrRv S τ (((tcrPermPows S perm)[e]!)[i]!) = (φ ^ e) (tcrRv S τ i) := by
  intro e he i hi
  have hsp := (tcrPermPows_spec S perm (fun j hj => (hperm j hj).1) e he).2 i hi
  rw [hsp]
  clear hsp he
  induction e with
  | zero => exact ⟨hi, by simp⟩
  | succ e ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hperm _ h1
    refine ⟨h3, ?_⟩
    rw [h4, h2, pow_succ']
    rfl

theorem tcrKindOfK_mem_tcrKindsOf (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) :
    tcrKindOfK (twistKindOf ρ Ψ) ∈ tcrKindsOf (compRank Ψ) Ψ.ncard := by
  unfold twistKindOf
  split_ifs with h1 h2 h3 h4
  · simp [tcrKindOfK, tcrKindsOf]
  · rcases h2 with ⟨ha, hb⟩ | ⟨ha, hb, hc⟩
    · simp [tcrKindOfK, tcrKindsOf, ha, hb]
    · simp [tcrKindOfK, tcrKindsOf, ha, hb]
  · obtain ⟨ha, hb⟩ := h3
    simp [tcrKindOfK, tcrKindsOf, ha, hb]
  · obtain ⟨ha, hb⟩ := h4
    simp [tcrKindOfK, tcrKindsOf, ha, hb]
  · simp [tcrKindOfK, tcrKindsOf]

theorem tcrCdataOf_sound
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (hφr : ∀ γ, IsRoot τ γ → IsRoot τ (φ γ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (psi : List ℕ) (hnd : psi.Nodup) (hlt : ∀ i ∈ psi, i < S.tcrN)
    (hΨ : IsRootComponent (tcrSet S τ psi)) {d : TcrCData}
    (h : tcrCdataOf S perm (tcrPermPows S perm) psi = some d) :
    TcDataOK ρ (tcrSet S τ psi) d := by
  unfold tcrCdataOf at h
  dsimp only at h
  by_cases hc : (tcrOrbitLen S.tcrN perm psi S.tcrN == 0 ||
      decide (12 < tcrOrbitLen S.tcrN perm psi S.tcrN)) = true
  · rw [if_pos hc] at h
    exact absurd h (by simp)
  · rw [if_neg hc] at h
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc
    obtain ⟨he0, he12⟩ := hc
    have hord := tcrOrbitLen_spec hG φ ρ hρ perm hperm psi hlt rfl he0
    refine ⟨hord.symm, tcrSimpleSys_length hG psi hnd hlt hΨ,
      (tcrSet_ncard hG psi hnd hlt).symm, ?_⟩
    have := tcrKindOf_sound hG φ hφr ρ hρ (tcrPermPows S perm) (tcrPows_rv φ perm hperm) psi hnd
      hlt hΨ hord.symm (Nat.le_of_not_lt (by simpa using he12)) hk
    simp [this]

theorem tcrCdataOfA_sound
    (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (psi : List ℕ) (hnd : psi.Nodup) (hlt : ∀ i ∈ psi, i < S.tcrN)
    (hΨ : IsRootComponent (tcrSet S τ psi)) {d : TcrCData}
    (h : tcrCdataOfA S perm psi = some d) : TcDataOK ρ (tcrSet S τ psi) d := by
  unfold tcrCdataOfA at h
  dsimp only at h
  by_cases hc : (tcrOrbitLen S.tcrN perm psi S.tcrN == 0) = true
  · rw [if_pos hc] at h
    exact absurd h (by simp)
  · rw [if_neg hc] at h
    have hd := Option.some.inj h
    subst hd
    have he0 : tcrOrbitLen S.tcrN perm psi S.tcrN ≠ 0 := by simpa using hc
    have hord := tcrOrbitLen_spec hG φ ρ hρ perm hperm psi hlt rfl he0
    have hr := (tcrSimpleSys_length hG psi hnd hlt hΨ)
    have hn := (tcrSet_ncard hG psi hnd hlt)
    refine ⟨hord.symm, hr, hn.symm, ?_⟩
    simp only
    rw [hr, ← hn]
    exact tcrKindOfK_mem_tcrKindsOf ρ _

end CdSound

end CFSG.StandardType.TableCRes

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Ker

variable {τ : Tag} {S : TcrSys} {p : ℕ}

theorem mem_tcrVecsMod (p : ℕ) : ∀ (k : ℕ) (l : List ℕ),
    l ∈ tcrVecsMod p k ↔ l.length = k ∧ ∀ x ∈ l, x < p
  | 0, l => by
    simp only [tcrVecsMod, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -⟩
      exact h
  | k + 1, l => by
    simp only [tcrVecsMod, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, l', hl', rfl⟩
      obtain ⟨h1, h2⟩ := (mem_tcrVecsMod p k l').1 hl'
      refine ⟨by simp [h1], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact h2 x hx
    · rintro ⟨h1, h2⟩
      cases l with
      | nil => simp at h1
      | cons a l' =>
        refine ⟨a, h2 a List.mem_cons_self, l', (mem_tcrVecsMod p k l').2
          ⟨by simpa using h1, fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩, rfl⟩

theorem tc_find_congr {α : Type*} (q q' : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, q x = q' x) → l.find? q = l.find? q'
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons]
    rw [h x List.mem_cons_self, tc_find_congr q q' l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem tcrNormVec_props [Fact p.Prime] (v : List ℕ) (hv : ∀ x ∈ v, x < p)
    (hv0 : ∃ x ∈ v, x ≠ 0) :
    (tcrNormVec p v).length = v.length ∧ (∀ x ∈ tcrNormVec p v, x < p) ∧
      tcrIsNorm (tcrNormVec p v) = true := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := hpp.pos
  unfold tcrNormVec
  obtain ⟨x0, hx0, hx0ne⟩ := hv0
  have hfind : (v.find? fun x => x != 0).isSome = true :=
    List.find?_isSome.2 ⟨x0, hx0, by simpa using hx0ne⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hfind
  rw [ha]
  have haspec := List.find?_some ha
  simp only [bne_iff_ne, ne_eq] at haspec
  have haM := List.mem_of_find?_eq_some ha
  have hap := hv a haM
  have hunit : ((a : ZMod p)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact haspec (Nat.eq_zero_of_dvd_of_lt h hap)
  set inv : ℕ := ((a : ZMod p)⁻¹).val with hinv
  have hinvp : inv < p := ZMod.val_lt _
  have hinvok : inv * a % p = 1 := by
    have : ((inv * a : ℕ) : ZMod p) = 1 := by
      push_cast
      rw [hinv, ZMod.natCast_zmod_val]
      exact inv_mul_cancel₀ hunit
    have h2 := (ZMod.natCast_eq_natCast_iff' (inv * a) 1 p).1 (by simpa using this)
    rw [h2]
    exact Nat.mod_eq_of_lt hpp.one_lt
  have hex : ((List.range p).find? fun c => c * a % p == 1).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨inv, List.mem_range.2 hinvp, by simpa using hinvok⟩
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hex
  have hc0spec := List.find?_some hc0
  simp only [beq_iff_eq] at hc0spec
  simp only [hc0, Option.getD_some]
  refine ⟨by simp, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact Nat.mod_lt _ hp0
  · unfold tcrIsNorm
    rw [List.find?_map]
    have hcong : v.find? ((fun x => x != 0) ∘ fun x => c0 * x % p) = v.find? (fun x => x != 0) := by
      apply tc_find_congr
      intro x hx
      simp only [Function.comp]
      by_cases hx0 : x = 0
      · subst hx0
        simp
      · have hne : c0 * x % p ≠ 0 := by
          intro h0
          have hxp := hv x hx
          have hdvd : p ∣ c0 * x := Nat.dvd_of_mod_eq_zero h0
          rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h1 | h1
          · have : p ∣ c0 * a := Dvd.dvd.mul_right h1 a
            rw [Nat.dvd_iff_mod_eq_zero, hc0spec] at this
            exact absurd this (by norm_num)
          · exact hx0 (Nat.eq_zero_of_dvd_of_lt h1 hxp)
        have h1 : (c0 * x % p != 0) = true := by simpa using hne
        have h2 : (x != 0) = true := by simpa using hx0
        rw [h1, h2]
    rw [hcong, ha]
    simp [hc0spec]

theorem tcrKernelLines_mem
    (hG : TcrGood τ S) [Fact p.Prime] (r : ℕ)
    (φ : AddMonoid.End (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ)
    (t : List ℕ) (ht : ∀ j : Fin τ.rank, t.getD j.val 0 < S.tcrN ∧
      tcrRv S τ (t.getD j.val 0) = φ (Pi.single j 1 : Fin τ.rank → ℤ))
    (v : Fin τ.rank → ZMod p) (hv0 : v ≠ 0)
    (hfr : ∀ j : Fin τ.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = (r : ZMod p) * v j) :
    ∃ l ∈ tcrKernelLines S (tcrNormVecs p τ.rank) p r t, ∃ c : ZMod p, c ≠ 0 ∧
      tcrVecOf τ p l = c • v := by
  classical
  have hpp : p.Prime := Fact.out
  set l0 : List ℕ := List.ofFn fun k : Fin τ.rank => (v k).val with hl0
  have hl0len : l0.length = τ.rank := by simp [hl0]
  have hl0lt : ∀ x ∈ l0, x < p := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact ZMod.val_lt _
  have hvec0 : tcrVecOf τ p l0 = v := by
    funext k
    simp only [tcrVecOf, hl0, tcr_getD_ofFn_nat]
    exact ZMod.natCast_zmod_val _
  have hl0nz : ∃ x ∈ l0, x ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
    refine ⟨(v k).val, List.mem_ofFn.2 ⟨k, rfl⟩, fun h => hk ?_⟩
    exact (ZMod.val_eq_zero (v k)).1 h
  obtain ⟨c, hc, hcv⟩ := tcrNormVec_spec l0 hl0lt (by rw [hvec0]; exact hv0)
  obtain ⟨hnlen, hnlt, hnnorm⟩ := tcrNormVec_props l0 hl0lt hl0nz
  have hcv' : tcrVecOf τ p (tcrNormVec p l0) = c • v := by rw [hcv, hvec0]
  refine ⟨tcrNormVec p l0, ?_, c, hc, hcv'⟩
  unfold tcrKernelLines
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold tcrNormVecs
    rw [List.mem_filter]
    exact ⟨(mem_tcrVecsMod p τ.rank _).2 ⟨by rw [hnlen, hl0len], hnlt⟩, hnnorm⟩
  · unfold tcrKerCond
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro j hj
    have hjt : j < τ.rank := by rw [← hG.rank]; exact hj
    obtain ⟨htN, hrv⟩ := ht ⟨j, hjt⟩
    have hroot : S.roots[t.getD j 0]! =
        List.ofFn (φ (Pi.single ⟨j, hjt⟩ 1 : Fin τ.rank → ℤ)) := by
      rw [(hG.rv_spec htN).2, hrv]
    rw [hroot, tcrDotNZ_ofFn _ (by rw [hnlen, hl0len])]
    have hρj : ρ (Pi.single ⟨j, hjt⟩ 1) = φ (Pi.single ⟨j, hjt⟩ 1 : Fin τ.rank → ℤ) :=
      hρ _ (isRoot_single τ _)
    apply Int.emod_eq_zero_of_dvd
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hlv : ∀ k : Fin τ.rank, (((tcrNormVec p l0).getD k.val 0 : ℕ) : ZMod p) = c * v k := by
      intro k
      have := congrFun hcv' k
      simpa [tcrVecOf] using this
    push_cast
    simp only [hlv]
    have h1 := hfr ⟨j, hjt⟩
    rw [hρj] at h1
    have hlj : (((tcrNormVec p l0).getD j 0 : ℕ) : ZMod p) = c * v ⟨j, hjt⟩ := hlv ⟨j, hjt⟩
    rw [hlj]
    calc ∑ k : Fin τ.rank, c * v k * (((φ (Pi.single ⟨j, hjt⟩ 1 : Fin τ.rank → ℤ)) k : ℤ) : ZMod p)
          - (r : ZMod p) * (c * v ⟨j, hjt⟩)
        = c * (∑ k : Fin τ.rank, (((φ (Pi.single ⟨j, hjt⟩ 1 : Fin τ.rank → ℤ)) k : ℤ) : ZMod p)
            * v k) - c * ((r : ZMod p) * v ⟨j, hjt⟩) := by
          rw [Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun k _ => by ring
          · ring
      _ = 0 := by rw [h1]; ring

end Ker

end CFSG.StandardType.TableCRes

end
