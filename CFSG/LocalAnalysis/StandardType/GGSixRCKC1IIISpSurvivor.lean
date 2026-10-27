module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpSurvivorAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpRad
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Klein
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair
public import CFSG.HardMathSupport.Kantor79.LongRootGroup

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.LieType.BorelTits CFSG.StandardType.RCKK1IIISp
  CFSG.StandardType.LieKnownR2.Short CFSG.QuasithinUnique.B113Lie.Sp
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open scoped Matrix

variable {m : ℕ}

theorem spRange_pair_eq (x y : SpMod m) :
    Set.range ![x, y] = ({x, y} : Set (SpMod m)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem spFinrank_span_pair (x y : SpMod m)
    (hli : LinearIndependent (GaloisField 2 1) ![x, y]) :
    Module.finrank (GaloisField 2 1) (Submodule.span (GaloisField 2 1) {x, y}) = 2 := by
  rw [← spRange_pair_eq, finrank_span_eq_card hli]
  simp

theorem spOrthogonal_inf_orthogonal (U T : Submodule (GaloisField 2 1) (SpMod m)) :
    (spBilin m).orthogonal U ⊓ (spBilin m).orthogonal T =
      (spBilin m).orthogonal (U ⊔ T) := by
  ext v
  rw [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff,
    LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    rw [(spBilin m).add_left, h1 u hu, h2 t ht, add_zero]
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun t ht => h t (Submodule.mem_sup_right ht)⟩

theorem spMul_eq_of_one_add_mul_one_add {E : Type*} [Ring E] {M N : E}
    (h : (1 + M) * (1 + N) = (1 + N) * (1 + M)) : M * N = N * M := by
  have h1 : 1 + ((M + N) + M * N) = (1 + M) * (1 + N) := by noncomm_ring
  have h2 : 1 + ((M + N) + N * M) = (1 + N) * (1 + M) := by noncomm_ring
  have h3 : 1 + ((M + N) + M * N) = 1 + ((M + N) + N * M) := by rw [h1, h, h2]
  exact add_left_cancel (add_left_cancel h3)

theorem spAltMap_mul_spAltMap (w b c : SpMod m) (hwb : spB m w b = 0) (hwc : spB m w c = 0)
    (v : SpMod m) :
    (spAltMap w b * spAltMap w c) v = (spB m v w * spB m b c) • w := by
  rw [Module.End.mul_apply, spAltMap_apply, spAltMap_apply, spB_add_left, spB_add_left,
    spB_smul_left, spB_smul_left, spB_smul_left, spB_smul_left, hwb,
    show spB m c w = 0 from spB_refl hwc, spB_self, spB_symm (m := m) c b]
  simp

theorem spZpowers_sup_eq_of_fourGroup {r s : SpG m} {V : Subgroup (SpG m)}
    (hrV : r ∈ V) (hsV : s ∈ V) (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hsZ : s ∉ Subgroup.zpowers r) (hV4 : Nat.card V = 4) :
    V = Subgroup.zpowers r ⊔ Subgroup.zpowers s := by
  have hcl : Subgroup.closure ({r, s} : Set (SpG m)) = V :=
    ggClosure_pair_eq (p := 2) Nat.prime_two (D := V) (d := r) (y := s)
      (by rw [hV4]; norm_num) hrV hsV hr1 (by simpa [pow_two] using hr2) hsZ
  have hpair : ({r} ∪ {s} : Set (SpG m)) = {r, s} := by
    ext x
    simp [or_comm]
  have hsup : Subgroup.zpowers r ⊔ Subgroup.zpowers s =
      Subgroup.closure ({r, s} : Set (SpG m)) := by
    calc Subgroup.zpowers r ⊔ Subgroup.zpowers s
        = Subgroup.closure {r} ⊔ Subgroup.closure {s} := by
          rw [Subgroup.zpowers_eq_closure r, Subgroup.zpowers_eq_closure s]
      _ = Subgroup.closure ({r} ∪ {s}) := (Subgroup.closure_union {r} {s}).symm
      _ = Subgroup.closure ({r, s} : Set (SpG m)) := by rw [hpair]
  rw [hsup, hcl]

theorem exists_isotropic_triple_of_pure_shortRoot_fourGroup
    {V : Subgroup (SpG m)} {r : SpG m}
    (hrV : r ∈ V) (hr1 : r ≠ 1) (hVab : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hpure : ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v) :
    ∃ (a b c : SpMod m) (s : SpG m), s ∈ V ∧ s ∉ Subgroup.zpowers r ∧
      LinearIndependent (GaloisField 2 1) ![a, b, c] ∧
      spB m a b = 0 ∧ spB m a c = 0 ∧ spB m b c = 0 ∧
      SpSiegel a b r ∧ SpSiegel a c s ∧
      V = Subgroup.zpowers r ⊔ Subgroup.zpowers s := by
  classical
  haveI : Finite (SpG m) := Subtype.finite
  have hr2 : r * r = 1 := by simpa [pow_two] using hVab.2 r hrV
  have hZcard : Nat.card (Subgroup.zpowers r) = 2 := by
    have horder : orderOf r = 2 := by
      rw [orderOf_eq_iff (by norm_num : 0 < 2)]
      refine ⟨?_, ?_⟩
      · simpa [pow_two] using hr2
      · intro k hk hk2
        have hk1 : k = 1 := by omega
        subst hk1
        simpa using hr1
    rw [Nat.card_zpowers, horder]
  have hnotle : ¬ V ≤ Subgroup.zpowers r := by
    intro hle
    have hcard : Nat.card V ≤ Nat.card (Subgroup.zpowers r) := Subgroup.card_le_of_le hle
    omega
  obtain ⟨s, hsV, hsZ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hs1 : s ≠ 1 := fun h => hsZ (by rw [h]; exact Subgroup.one_mem _)
  have hcomm : r * s = s * r := by
    have h := hVab.1.is_comm.comm ⟨r, hrV⟩ ⟨s, hsV⟩
    simpa using congrArg (fun z : V => (z : SpG m)) h
  obtain ⟨a, b, hBab, hr⟩ := hpure r hrV hr1
  obtain ⟨x, y, hBxy, hs⟩ := hpure s hsV hs1
  have haLI : LinearIndependent (GaloisField 2 1) ![a, b] := spSiegel_li hr hr1
  have hxLI : LinearIndependent (GaloisField 2 1) ![x, y] := spSiegel_li hs hs1
  let U : Submodule (GaloisField 2 1) (SpMod m) := Submodule.span (GaloisField 2 1) {a, b}
  let T : Submodule (GaloisField 2 1) (SpMod m) := Submodule.span (GaloisField 2 1) {x, y}
  have hU2 : Module.finrank (GaloisField 2 1) U = 2 := spFinrank_span_pair a b haLI
  have hT2 : Module.finrank (GaloisField 2 1) T = 2 := spFinrank_span_pair x y hxLI
  have hWU : (spForm m (GaloisField 2 1)).IsTotallyIsotropic U :=
    spForm_totallyIsotropic_span a b hBab
  have hWT : (spForm m (GaloisField 2 1)).IsTotallyIsotropic T :=
    spForm_totallyIsotropic_span x y hBxy
  have hMle : LinearMap.range (spAltMap a b) ≤ U := by
    rw [spAltMap_range a b haLI hBab]
  have hNle : LinearMap.range (spAltMap x y) ≤ T := by
    rw [spAltMap_range x y hxLI hBxy]
  have hrsV : r * s ∈ V := V.mul_mem hrV hsV
  have hrs1 : r * s ≠ 1 := by
    intro h
    have hs_eq : s = r := by
      calc s = 1 * s := by rw [one_mul]
        _ = (r * r) * s := by rw [hr2]
        _ = r * (r * s) := by group
        _ = r * 1 := by rw [h]
        _ = r := by rw [mul_one]
    exact hsZ (by rw [hs_eq]; exact Subgroup.mem_zpowers r)
  obtain ⟨p, q, hBpq, hrs⟩ := hpure (r * s) hrsV hrs1
  have hpqLI : LinearIndependent (GaloisField 2 1) ![p, q] := spSiegel_li hrs hrs1
  by_cases hdisj : U ⊓ T = ⊥
  · exfalso
    have hMnat : natRep (StatedSp m (GaloisField 2 1)) r - 1 = spAltMap a b := by
      rw [spAltMap_natRep hr, add_sub_cancel_left]
    have hNnat : natRep (StatedSp m (GaloisField 2 1)) s - 1 = spAltMap x y := by
      rw [spAltMap_natRep hs, add_sub_cancel_left]
    have hcommEnd : (1 + spAltMap a b) * (1 + spAltMap x y) =
        (1 + spAltMap x y) * (1 + spAltMap a b) := by
      have h1 : natRep (StatedSp m (GaloisField 2 1)) r *
          natRep (StatedSp m (GaloisField 2 1)) s =
          natRep (StatedSp m (GaloisField 2 1)) s *
            natRep (StatedSp m (GaloisField 2 1)) r := by
        rw [← map_mul, ← map_mul, hcomm]
      rwa [spAltMap_natRep hr, spAltMap_natRep hs] at h1
    have hMN : spAltMap a b * spAltMap x y = spAltMap x y * spAltMap a b :=
      spMul_eq_of_one_add_mul_one_add hcommEnd
    have hMN0 : spAltMap a b * spAltMap x y = 0 := by
      have hle : LinearMap.range (spAltMap a b * spAltMap x y) ≤ U ⊓ T := by
        apply le_inf
        · rintro _ ⟨v, rfl⟩
          exact hMle ⟨spAltMap x y v, rfl⟩
        · rw [hMN]
          rintro _ ⟨v, rfl⟩
          exact hNle ⟨spAltMap a b v, rfl⟩
      rw [hdisj, le_bot_iff] at hle
      apply LinearMap.ext
      intro v
      have hv : (spAltMap a b * spAltMap x y) v ∈
          LinearMap.range (spAltMap a b * spAltMap x y) := ⟨v, rfl⟩
      rw [hle] at hv
      simpa using hv
    have hkerSum : LinearMap.ker (spAltMap a b + spAltMap x y) =
        LinearMap.ker (spAltMap a b) ⊓ LinearMap.ker (spAltMap x y) := by
      ext v
      rw [LinearMap.mem_ker, LinearMap.add_apply, Submodule.mem_inf, LinearMap.mem_ker,
        LinearMap.mem_ker]
      constructor
      · intro h
        have h1 : spAltMap a b v = spAltMap x y v := by
          calc spAltMap a b v =
                spAltMap a b v + (spAltMap x y v + spAltMap x y v) := by
                rw [spAdd_self_eq_zero, add_zero]
            _ = (spAltMap a b v + spAltMap x y v) + spAltMap x y v := by abel
            _ = spAltMap x y v := by rw [h, zero_add]
        have hMv : spAltMap a b v ∈ U := hMle ⟨v, rfl⟩
        have hNv : spAltMap x y v ∈ T := hNle ⟨v, rfl⟩
        have hboth : spAltMap a b v ∈ U ⊓ T := ⟨hMv, h1 ▸ hNv⟩
        rw [hdisj] at hboth
        have hzero : spAltMap a b v = 0 := by simpa using hboth
        exact ⟨hzero, by rw [← h1]; exact hzero⟩
      · rintro ⟨h1, h2⟩
        simp [h1, h2]
    have hkerM : LinearMap.ker (spAltMap a b) = (spBilin m).orthogonal U :=
      spAltMap_ker a b haLI
    have hkerN : LinearMap.ker (spAltMap x y) = (spBilin m).orthogonal T :=
      spAltMap_ker x y hxLI
    have hdimV : Module.finrank (GaloisField 2 1) (SpMod m) = 2 * m := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hdimsup : Module.finrank (GaloisField 2 1) ↥(U ⊔ T) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (s := U) (t := T)
      rw [hU2, hT2, hdisj, finrank_bot] at h
      omega
    have hkerdim : Module.finrank (GaloisField 2 1)
        (LinearMap.ker (spAltMap a b + spAltMap x y)) = 2 * m - 4 := by
      rw [hkerSum, hkerM, hkerN, spOrthogonal_inf_orthogonal,
        LinearMap.BilinForm.finrank_orthogonal spBilin_nondegenerate, hdimV, hdimsup]
    have hrank : Module.finrank (GaloisField 2 1)
        (LinearMap.range (spAltMap a b + spAltMap x y)) = 4 := by
      have h := LinearMap.finrank_range_add_finrank_ker (spAltMap a b + spAltMap x y)
      have hle := Submodule.finrank_mono (show U ⊔ T ≤ ⊤ from le_top)
      rw [hdimsup, finrank_top, hdimV] at hle
      rw [hkerdim, hdimV] at h
      omega
    have hnatrs : natRep (StatedSp m (GaloisField 2 1)) (r * s) =
        1 + (spAltMap a b + spAltMap x y) := by
      rw [map_mul, spAltMap_natRep hr, spAltMap_natRep hs]
      calc (1 + spAltMap a b) * (1 + spAltMap x y) =
            1 + (spAltMap a b + spAltMap x y) + spAltMap a b * spAltMap x y := by
              noncomm_ring
        _ = 1 + (spAltMap a b + spAltMap x y) := by rw [hMN0, add_zero]
    have hsubrs : natRep (StatedSp m (GaloisField 2 1)) (r * s) - 1 =
        spAltMap a b + spAltMap x y := by
      rw [hnatrs, add_sub_cancel_left]
    have hrange2 : Module.finrank (GaloisField 2 1)
        (LinearMap.range (spAltMap a b + spAltMap x y)) = 2 := by
      rw [← hsubrs, spSiegel_range hrs hrs1 hBpq]
      exact spFinrank_span_pair p q hpqLI
    omega
  · obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdisj
    have hwU : w ∈ U := (Submodule.mem_inf.mp hwP).1
    have hwT : w ∈ T := (Submodule.mem_inf.mp hwP).2
    by_cases hUT : U ≤ T
    · exfalso
      have hTU : U = T := Submodule.eq_of_le_of_finrank_eq hUT (by rw [hU2, hT2])
      have hrs_eq : r = s := by
        refine spSiegel_eq_of_span_eq hr hr1 hs hs1 ?_
        have h := hTU.symm
        simpa only [U, T] using h
      exact hsZ (by rw [← hrs_eq]; exact Subgroup.mem_zpowers r)
    · obtain ⟨b, hbU, hbLI, hbspan⟩ :=
        exists_pair_of_mem_of_finrank_eq_two (A := U) hU2 hwU hw0
      obtain ⟨c, hcT, hcLI, hcspan⟩ :=
        exists_pair_of_mem_of_finrank_eq_two (A := T) hT2 hwT hw0
      have hwU' : w ∈ U := by rw [← hbspan]; exact Submodule.subset_span (by simp)
      have hwT' : w ∈ T := by rw [← hcspan]; exact Submodule.subset_span (by simp)
      have hBwb : spB m w b = 0 := by
        rw [spB_eq_spForm]
        exact (spForm m (GaloisField 2 1)).refl b w (hWU hwU' b hbU)
      have hBwc : spB m w c = 0 := by
        rw [spB_eq_spForm]
        exact (spForm m (GaloisField 2 1)).refl c w (hWT hwT' c hcT)
      have hb0 : b ≠ 0 := by
        intro hb
        have h := (LinearIndependent.pair_iff.mp hbLI) 0 1 (by simp [hb])
        exact one_ne_zero h.2
      have hwbne : w ≠ b := by
        intro h
        have h0 : (1 : GaloisField 2 1) • w + (1 : GaloisField 2 1) • b = 0 := by
          rw [one_smul, one_smul, h]
          exact spAdd_self_eq_zero b
        have h := (LinearIndependent.pair_iff.mp hbLI) 1 1 h0
        exact one_ne_zero h.1
      have hcspan' : c ∉ Submodule.span (GaloisField 2 1) {w} := by
        rw [Submodule.mem_span_singleton]
        rintro ⟨α, hα⟩
        exact (LinearIndependent.pair_iff' hw0).mp hcLI α hα
      have hUeqT_of_mem {z : SpMod m} (hzU : z ∈ U) (hzT : z ∈ T)
          (hzLI : LinearIndependent (GaloisField 2 1) ![w, z]) : U = T := by
        have hzP : z ∈ U ⊓ T := ⟨hzU, hzT⟩
        have hwz_le : Submodule.span (GaloisField 2 1) {w, z} ≤ U ⊓ T := by
          rw [Submodule.span_le]
          intro y hy
          rcases hy with hy | hy
          · rw [hy]; exact hwP
          · rw [hy]; exact hzP
        have hP2eq : Module.finrank (GaloisField 2 1) ↥(U ⊓ T) = 2 := by
          have hge : 2 ≤ Module.finrank (GaloisField 2 1) ↥(U ⊓ T) := by
            have h := Submodule.finrank_mono hwz_le
            rwa [spFinrank_span_pair w z hzLI] at h
          have hle : Module.finrank (GaloisField 2 1) ↥(U ⊓ T) ≤ 2 := by
            have h := Submodule.finrank_mono (show U ⊓ T ≤ T from inf_le_right)
            rwa [hT2] at h
          omega
        have hTU : T ≤ U := by
          have hPT : U ⊓ T = T :=
            Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hP2eq, hT2])
          rw [← hPT]
          exact inf_le_left
        exact (Submodule.eq_of_le_of_finrank_eq hTU (by rw [hT2, hU2])).symm
      have hcU : c ∉ U := by
        intro hcU'
        exact hUT (le_of_eq (hUeqT_of_mem hcU' hcT hcLI))
      have hBwb' : SpSiegel w b r := by
        obtain ⟨t, ht⟩ := spSiegel_exists (m := m) (x := w) (y := b) hBwb
        have ht1 : t ≠ 1 := by
          intro h
          have hd := (spSiegel_eq_one_iff ht).mp h
          rcases hd with h0 | h0 | h0
          · exact hw0 h0
          · exact hb0 h0
          · exact hwbne h0
        have hrt : r = t := by
          refine spSiegel_eq_of_span_eq hr hr1 ht ht1 ?_
          rw [hbspan]
        rw [hrt]
        exact ht
      have hBwc' : SpSiegel w c s := by
        obtain ⟨u, hu⟩ := spSiegel_exists (m := m) (x := w) (y := c) hBwc
        have hc0 : c ≠ 0 := by
          intro hc
          exact hcspan' (by rw [hc]; exact Submodule.zero_mem _)
        have hwcne : w ≠ c := by
          intro h
          have h0 : (1 : GaloisField 2 1) • w + (1 : GaloisField 2 1) • c = 0 := by
            rw [one_smul, one_smul, h]
            exact spAdd_self_eq_zero c
          have h := (LinearIndependent.pair_iff.mp hcLI) 1 1 h0
          exact one_ne_zero h.1
        have hu1 : u ≠ 1 := by
          intro h
          have hd := (spSiegel_eq_one_iff hu).mp h
          rcases hd with h0 | h0 | h0
          · exact hw0 h0
          · exact hc0 h0
          · exact hwcne h0
        have hsu : s = u := by
          refine (spSiegel_eq_of_span_eq (a := w) (b := c) (x := x) (y := y)
            (r := u) (s := s) hu hu1 hs hs1 ?_).symm
          rw [hcspan]
        rw [hsu]
        exact hu
      have hbspanU : Submodule.span (GaloisField 2 1) {w, b} = U := hbspan
      have hcspanT : Submodule.span (GaloisField 2 1) {w, c} = T := hcspan
      have hbc0 : b + c ≠ 0 := by
        intro h
        have hbc : b = c := by
          have h1 : b + c + c = c := by rw [h, zero_add]
          rwa [add_assoc, spAdd_self_eq_zero, add_zero] at h1
        exact hUT (le_of_eq (hUeqT_of_mem hbU (by rw [hbc]; exact hcT) hbLI))
      have hwbc : w ≠ b + c := by
        intro h
        have hcU' : c ∈ U := by
          have hc_eq : c = w + b := by
            calc c = 0 + c := by rw [zero_add]
              _ = (b + b) + c := by rw [spAdd_self_eq_zero]
              _ = b + (b + c) := by abel
              _ = b + w := by rw [← h]
              _ = w + b := by rw [add_comm]
          rw [hc_eq]
          exact U.add_mem hwU hbU
        exact hcU hcU'
      have hliwb : LinearIndependent (GaloisField 2 1) ![w, b + c] := by
        rw [LinearIndependent.pair_iff' hw0]
        intro α hα
        rcases rck1416_gf2_eq_zero_or_one α with hα0 | hα1
        · rw [hα0, zero_smul] at hα
          exact hbc0 hα.symm
        · rw [hα1, one_smul] at hα
          exact hwbc hα
      have hBwbc : spB m w (b + c) = 0 := by
        rw [spB_add_right, hBwb, hBwc, add_zero]
      obtain ⟨v, v', hv_w, hv_bc, -, -, -⟩ := exists_spDualPair w (b + c) hliwb hBwbc
      have hv_w' : spB m v w = 1 := by
        rw [spB_symm (m := m) v w]
        exact hv_w
      have hv_bc' : spB m v (b + c) = 0 := by
        rw [spB_symm (m := m) v (b + c)]
        exact hv_bc
      have hval : (natRep (StatedSp m (GaloisField 2 1)) (r * s) - 1) v =
          b + c + spB m b c • w := by
        have hnatrs2 : natRep (StatedSp m (GaloisField 2 1)) (r * s) =
            1 + (spAltMap w b + spAltMap w c + spAltMap w b * spAltMap w c) := by
          rw [map_mul, spAltMap_natRep hBwb', spAltMap_natRep hBwc']
          noncomm_ring
        have hsubrs2 : natRep (StatedSp m (GaloisField 2 1)) (r * s) - 1 =
            spAltMap w b + spAltMap w c + spAltMap w b * spAltMap w c := by
          rw [hnatrs2, add_sub_cancel_left]
        have hMNv : (spAltMap w b * spAltMap w c) v = spB m b c • w := by
          rw [spAltMap_mul_spAltMap w b c hBwb hBwc v, hv_w', one_mul]
        rw [hsubrs2, LinearMap.add_apply, ← spAltMap_add_right w b c, spAltMap_apply, hMNv,
          hv_bc', hv_w']
        simp [add_assoc]
      have hpure_rs : spB m v ((natRep (StatedSp m (GaloisField 2 1)) (r * s) - 1) v) = 0 := by
        have h := spSiegel_beta_moved hrs v
        rw [spAct_eq_natRep] at h
        simpa only [LinearMap.sub_apply, Module.End.one_apply] using h
      have hbc_final : spB m b c = 0 := by
        have hp : spB m v (b + c + spB m b c • w) = 0 := by
          rw [← hval]
          exact hpure_rs
        simpa only [spB_add_right, spB_smul_right, hv_bc', hv_w', mul_one, zero_add] using hp
      have hlic : LinearIndependent (GaloisField 2 1) ![w, b, c] := by
        have hc_range : c ∉ Submodule.span (GaloisField 2 1) (Set.range ![w, b]) := by
          rw [spRange_pair_eq, hbspan]
          exact hcU
        have h := LinearIndependent.finSnoc (v := ![w, b]) hbLI hc_range
        simpa [Fin.snoc, Fin.cons] using h
      exact ⟨w, b, c, s, hsV, hsZ, hlic, hBwb, hBwc, hbc_final, hBwb', hBwc',
        spZpowers_sup_eq_of_fourGroup hrV hsV hr1 hr2 hsZ hV4⟩

theorem spAct_mem_span_of_commutes {r g : SpG m} {a b : SpMod m}
    (hr : SpSiegel a b r) (hr1 : r ≠ 1) (hBab : spB m a b = 0) (hcomm : g * r = r * g) :
    ∀ u ∈ Submodule.span (GaloisField 2 1) {a, b},
      spAct g u ∈ Submodule.span (GaloisField 2 1) {a, b} := by
  have haLI : LinearIndependent (GaloisField 2 1) ![a, b] := spSiegel_li hr hr1
  have hcommEnd : natRep (StatedSp m (GaloisField 2 1)) g *
      natRep (StatedSp m (GaloisField 2 1)) r =
      natRep (StatedSp m (GaloisField 2 1)) r *
        natRep (StatedSp m (GaloisField 2 1)) g := by
    rw [← map_mul, ← map_mul, hcomm]
  have hgM : natRep (StatedSp m (GaloisField 2 1)) g * spAltMap a b =
      spAltMap a b * natRep (StatedSp m (GaloisField 2 1)) g := by
    have h1 : natRep (StatedSp m (GaloisField 2 1)) g * (1 + spAltMap a b) =
        (1 + spAltMap a b) * natRep (StatedSp m (GaloisField 2 1)) g := by
      rwa [spAltMap_natRep hr] at hcommEnd
    have h2 : natRep (StatedSp m (GaloisField 2 1)) g +
          natRep (StatedSp m (GaloisField 2 1)) g * spAltMap a b =
        natRep (StatedSp m (GaloisField 2 1)) g +
          spAltMap a b * natRep (StatedSp m (GaloisField 2 1)) g := by
      calc natRep (StatedSp m (GaloisField 2 1)) g +
            natRep (StatedSp m (GaloisField 2 1)) g * spAltMap a b =
            natRep (StatedSp m (GaloisField 2 1)) g * (1 + spAltMap a b) := by
              noncomm_ring
        _ = (1 + spAltMap a b) * natRep (StatedSp m (GaloisField 2 1)) g := h1
        _ = natRep (StatedSp m (GaloisField 2 1)) g +
            spAltMap a b * natRep (StatedSp m (GaloisField 2 1)) g := by noncomm_ring
    exact add_left_cancel h2
  intro u hu
  have hu' : u ∈ LinearMap.range (spAltMap a b) := by
    rw [spAltMap_range a b haLI hBab]
    exact hu
  obtain ⟨v, rfl⟩ := hu'
  have happ : spAct g (spAltMap a b v) = spAltMap a b (spAct g v) := by
    have h := congrArg (fun e : SpMod m →ₗ[GaloisField 2 1] SpMod m => e v) hgM
    simpa only [Module.End.mul_apply, spAct_eq_natRep] using h
  rw [happ, ← spAltMap_range a b haLI hBab]
  exact ⟨spAct g v, rfl⟩

theorem spAct_commutes_of_mem_stabilizer {r g : SpG m} {a b : SpMod m}
    (hr : SpSiegel a b r) (hr1 : r ≠ 1) (hBab : spB m a b = 0)
    (hg : g ∈ SymplecticFlag.stabilizer m (GaloisField 2 1)
      (Submodule.span (GaloisField 2 1) {a, b})) :
    g * r = r * g := by
  have haLI : LinearIndependent (GaloisField 2 1) ![a, b] := spSiegel_li hr hr1
  have hgU : ∀ u ∈ Submodule.span (GaloisField 2 1) {a, b},
      spAct g u ∈ Submodule.span (GaloisField 2 1) {a, b} := by
    intro u hu
    have h := rep_mem_of_mem_stabilizer hg hu
    rwa [spAct_eq_natRep]
  have hginv : g⁻¹ ∈ SymplecticFlag.stabilizer m (GaloisField 2 1)
      (Submodule.span (GaloisField 2 1) {a, b}) := Subgroup.inv_mem _ hg
  have hgU' : ∀ u ∈ Submodule.span (GaloisField 2 1) {a, b},
      spAct g⁻¹ u ∈ Submodule.span (GaloisField 2 1) {a, b} := by
    intro u hu
    have h := rep_mem_of_mem_stabilizer hginv hu
    rwa [spAct_eq_natRep]
  have hspan_eq : Submodule.span (GaloisField 2 1) {spAct g a, spAct g b} =
      Submodule.span (GaloisField 2 1) {a, b} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with hz | hz
      · rw [hz]; exact hgU a (Submodule.subset_span (by simp))
      · rw [hz]; exact hgU b (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro u hu
      have hu' : spAct g⁻¹ u ∈ Submodule.span (GaloisField 2 1) {a, b} :=
        hgU' u (Submodule.subset_span hu)
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hu'
      have hu_eq : u = α • spAct g a + β • spAct g b := by
        calc u = spAct g (spAct g⁻¹ u) := (spAct_inv_apply g u).symm
          _ = spAct g (α • a + β • b) := by rw [← hαβ]
          _ = α • spAct g a + β • spAct g b := by
              rw [spAct_add, spAct_smul, spAct_smul]
      rw [hu_eq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hconj : SpSiegel (spAct g a) (spAct g b) (g * r * g⁻¹) := spSiegel_conj hr g
  have hconj1 : g * r * g⁻¹ ≠ 1 := by
    intro h
    have h1 : r = 1 := by
      calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h]
        _ = 1 := by group
    exact hr1 h1
  have heq : g * r * g⁻¹ = r := by
    refine spSiegel_eq_of_span_eq hconj hconj1 hr hr1 ?_
    exact hspan_eq.symm
  calc g * r = (g * r * g⁻¹) * g := by group
    _ = r * g := by rw [heq]

theorem spPureFourGroup_mem_iff {r s : SpG m} {V : Subgroup (SpG m)}
    (hrV : r ∈ V) (hsV : s ∈ V) (hr1 : r ≠ 1) (hr2 : r * r = 1) (hs2 : s * s = 1)
    (hsZ : s ∉ Subgroup.zpowers r) (hcomm : r * s = s * r) (hV4 : Nat.card V = 4) :
    ∀ v : SpG m, v ∈ V ↔ v = 1 ∨ v = r ∨ v = s ∨ v = r * s := by
  have hs1 : s ≠ 1 := fun h => hsZ (by rw [h]; exact Subgroup.one_mem _)
  have hne : r ≠ s := fun h => hsZ (by rw [← h]; exact Subgroup.mem_zpowers r)
  have hKmem : ∀ x : SpG m,
      x ∈ CFSG.Quasithin.kleinFour r s hr2 hs2 hcomm ↔
        x = 1 ∨ x = r ∨ x = s ∨ x = r * s := fun x => CFSG.Quasithin.mem_kleinFour
  have hKV : CFSG.Quasithin.kleinFour r s hr2 hs2 hcomm ≤ V := by
    intro x hx
    rw [hKmem x] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact V.one_mem
    · rw [hx]; exact hrV
    · rw [hx]; exact hsV
    · rw [hx]; exact V.mul_mem hrV hsV
  have hcardK : Nat.card (CFSG.Quasithin.kleinFour r s hr2 hs2 hcomm) = 4 :=
    CFSG.Quasithin.card_kleinFour (a := r) (b := s) (ha := hr2) (hb := hs2) (hab := hcomm)
      hr1 hs1 hne
  have hVK : V = CFSG.Quasithin.kleinFour r s hr2 hs2 hcomm :=
    (Subgroup.eq_of_le_of_card_ge hKV (by rw [hV4, hcardK])).symm
  intro v
  rw [hVK]
  exact hKmem v

theorem normalization_of_pure_shortRoot_fourGroup (hm : 3 ≤ m)
    {V : Subgroup (SpG m)} {r : SpG m}
    (hrV : r ∈ V) (hr1 : r ≠ 1) (hVab : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hpure : ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v) :
    CoreCommAt (⊤ : Subgroup (SpG m)) V r ∧
      pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) ≤
        Subgroup.normalizer (V : Set (SpG m)) := by
  classical
  obtain ⟨a, b, c, s, hsV, hsZ, hLI, hBab, hBac, hBbc, hr, hs, hVeq⟩ :=
    exists_isotropic_triple_of_pure_shortRoot_fourGroup hrV hr1 hVab hV4 hpure
  haveI : Finite (SpG m) := Subtype.finite
  have hr2 : r * r = 1 := by simpa [pow_two] using hVab.2 r hrV
  have hs2 : s * s = 1 := by simpa [pow_two] using hVab.2 s hsV
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h := hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg (fun z : V => (z : SpG m)) h
  have haLI : LinearIndependent (GaloisField 2 1) ![a, b] := spSiegel_li hr hr1
  let U : Submodule (GaloisField 2 1) (SpMod m) := Submodule.span (GaloisField 2 1) {a, b}
  have hW : (spForm m (GaloisField 2 1)).IsTotallyIsotropic U :=
    spForm_totallyIsotropic_span a b hBab
  obtain ⟨e, f, hpp⟩ := spPlanePair_of_isoPair a b haLI hBab
  have hcent : Subgroup.centralizer ({r} : Set (SpG m)) =
      SymplecticFlag.stabilizer m (GaloisField 2 1) U := by
    apply le_antisymm
    · intro g hg
      have hgr : g * r = r * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hgrinv : g⁻¹ * r = r * g⁻¹ := by
        calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * r) * g⁻¹ := by rw [← hgr]
          _ = r * g⁻¹ := by group
      refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (W := U) ?_ ?_
      · intro u hu
        have h := spAct_mem_span_of_commutes hr hr1 hBab hgr u hu
        simpa only [U, spAct] using h
      · intro u hu
        have h := spAct_mem_span_of_commutes hr hr1 hBab hgrinv u hu
        simpa only [U, spAct] using h
    · intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (spAct_commutes_of_mem_stabilizer hr hr1 hBab (by simpa only [U] using hg))
  have hcomm : r * s = s * r := hVcomm r hrV s hsV
  have hpCore_le : pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) ≤
      Subgroup.centralizer ({r} : Set (SpG m)) :=
    CFSG.StandardType.GGRootNorm.pCoreOf_le _
  have hpcore : pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) ≤ sprad U hW := by
    rw [hcent]
    exact pCoreOf_stabilizer_le_sprad (a₁ := a) (a₂ := b) (b₁ := e) (b₂ := f) hpp (hW := hW)
  have hcperp : c ∈ (spForm m (GaloisField 2 1)).perp U := by
    rw [ReflForm.mem_perp]
    intro w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    have h : spB m (α • a + β • b) c = 0 := by
      rw [spB_add_left, spB_smul_left, spB_smul_left, hBac, hBbc, mul_zero, mul_zero, add_zero]
    rwa [spB_eq_spForm] at h
  have hVmem := spPureFourGroup_mem_iff hrV hsV hr1 hr2 hs2 hsZ hcomm hV4
  have hkey : ∀ g ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))),
      (∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧
        ∀ v ∈ V, ∃ z ∈ Subgroup.zpowers r, g * v * g⁻¹ = v * z := by
    intro g hg
    have hgC : g ∈ Subgroup.centralizer ({r} : Set (SpG m)) := hpCore_le hg
    have hgrad : g ∈ sprad U hW := hpcore hg
    have hga : spAct g a = a := by
      rw [spAct_eq_natRep]
      exact (mem_rad.mp hgrad).1 a (Submodule.subset_span (by simp))
    have hgb : spAct g b = b := by
      rw [spAct_eq_natRep]
      exact (mem_rad.mp hgrad).1 b (Submodule.subset_span (by simp))
    set u : SpMod m := spAct g c - c with hu_def
    have huU : u ∈ U := by
      rw [hu_def, spAct_eq_natRep]
      exact (mem_rad.mp hgrad).2 c hcperp
    have hgc_eq : spAct g c = c + u := by rw [hu_def]; abel
    have hBau : spB m a u = 0 := by
      rw [spB_eq_spForm]
      exact (spForm m (GaloisField 2 1)).refl u a
        (hW (show a ∈ U from Submodule.subset_span (by simp)) u huU)
    obtain ⟨t, ht⟩ := spSiegel_exists (m := m) (x := a) (y := u) hBau
    have htZ : t ∈ Subgroup.zpowers r := by
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp huU
      rw [← hαβ] at ht
      rcases rck1416_gf2_eq_zero_or_one α with hα | hα <;>
        rcases rck1416_gf2_eq_zero_or_one β with hβ | hβ
      · rw [hα, hβ] at ht
        simp only [zero_smul, add_zero, zero_add] at ht
        have ht1 : t = 1 := spSiegel_ext ht (spSiegel_zero_right (m := m) (x := a))
        rw [ht1]; exact Subgroup.one_mem _
      · rw [hα, hβ] at ht
        simp only [zero_smul, one_smul, add_zero, zero_add] at ht
        have ht1 : t = r := spSiegel_ext ht hr
        rw [ht1]; exact Subgroup.mem_zpowers r
      · rw [hα, hβ] at ht
        simp only [zero_smul, one_smul, add_zero, zero_add] at ht
        have ht1 : t = 1 := spSiegel_ext ht (spSiegel_self (m := m) a)
        rw [ht1]; exact Subgroup.one_mem _
      · rw [hα, hβ] at ht
        simp only [one_smul, add_zero] at ht
        have hsum : SpSiegel a (a + b) r := by
          have h := spSiegel_mul (x := a) (y := a) (z := b) (spB_self a) hBab hBab
            (spSiegel_self a) hr
          simpa using h
        have ht1 : t = r := spSiegel_ext ht hsum
        rw [ht1]; exact Subgroup.mem_zpowers r
    have hBcu : spB m c u = 0 := by
      rw [spB_eq_spForm]
      exact (spForm m (GaloisField 2 1)).refl u c (hcperp u huU)
    have hgs : g * s * g⁻¹ = s * t := by
      have hconj := spSiegel_conj hs g
      rw [hga, hgc_eq] at hconj
      exact spSiegel_ext hconj (spSiegel_mul hBac hBau hBcu hs ht)
    have hgr : g * r * g⁻¹ = r := by
      have hconj := spSiegel_conj hr g
      rw [hga, hgb] at hconj
      exact spSiegel_ext hconj hr
    have htV : t ∈ V := Subgroup.zpowers_le.mpr hrV htZ
    constructor
    · intro v hv
      rw [hVmem v] at hv
      rcases hv with hv | hv | hv | hv
      · rw [hv]; simpa using V.one_mem
      · rw [hv, hgr]; exact hrV
      · rw [hv, hgs]; exact V.mul_mem hsV htV
      · rw [hv]
        have h_eq : g * (r * s) * g⁻¹ = (r * s) * t := by
          calc g * (r * s) * g⁻¹ = (g * r * g⁻¹) * (g * s * g⁻¹) := by group
            _ = r * (s * t) := by rw [hgr, hgs]
            _ = (r * s) * t := by group
        rw [h_eq]
        exact V.mul_mem (V.mul_mem hrV hsV) htV
    · intro v hv
      rw [hVmem v] at hv
      rcases hv with hv | hv | hv | hv
      · rw [hv]; exact ⟨1, Subgroup.one_mem _, by group⟩
      · rw [hv]; exact ⟨1, Subgroup.one_mem _, by rw [hgr, mul_one]⟩
      · rw [hv]; exact ⟨t, htZ, hgs⟩
      · rw [hv]
        exact ⟨t, htZ, by
          calc g * (r * s) * g⁻¹ = (g * r * g⁻¹) * (g * s * g⁻¹) := by group
            _ = r * (s * t) := by rw [hgr, hgs]
            _ = (r * s) * t := by group⟩
  constructor
  · intro v hv y hy
    have hy' : y ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) := by simpa using hy
    obtain ⟨z, hzZ, hz⟩ := (hkey y hy').2 v hv
    have hzV : z ∈ V := Subgroup.zpowers_le.mpr hrV hzZ
    have heq : v * y * v⁻¹ * y⁻¹ = z⁻¹ := by
      calc v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
        _ = v * (y * v * y⁻¹)⁻¹ := by group
        _ = v * (v * z)⁻¹ := by rw [hz]
        _ = z⁻¹ := by
            rw [mul_inv_rev, ← mul_assoc,
              hVcomm v hv z⁻¹ (Subgroup.inv_mem _ hzV), mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact Subgroup.inv_mem _ hzZ
  · intro y hy
    have hy' : y ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) := by simpa using hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact (hkey y hy').1 v hv
    · intro hv
      have hyinv : y⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) :=
        Subgroup.inv_mem _ hy'
      have h := (hkey y⁻¹ hyinv).1 (y * v * y⁻¹) hv
      rwa [show y⁻¹ * (y * v * y⁻¹) * (y⁻¹)⁻¹ = v by group] at h

theorem k2At_of_pure_shortRoot_fourGroup (hm : 3 ≤ m)
    {V : Subgroup (SpG m)} {r : SpG m}
    (hrV : r ∈ V) (hr1 : r ≠ 1) (hVab : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hpure : ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v) :
    pCoreOf 2 (Subgroup.centralizer ({r} : Set (SpG m))) ≤
      Subgroup.normalizer (V : Set (SpG m)) :=
  (normalization_of_pure_shortRoot_fourGroup hm hrV hr1 hVab hV4 hpure).2

theorem k2At_top_of_pure_shortRoot_fourGroup (hm : 3 ≤ m)
    {V : Subgroup (SpG m)} {r : SpG m}
    (hrV : r ∈ V) (hr1 : r ≠ 1) (hVab : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hpure : ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v) :
    K2At (⊤ : Subgroup (SpG m)) V r := by
  simpa [K2At] using k2At_of_pure_shortRoot_fourGroup hm hrV hr1 hVab hV4 hpure

end CFSG.StandardType.RCKC1
