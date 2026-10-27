module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def QT : Subgroup G := pCoreOf 2 X.GT

theorem QT_le_GT : X.QT ≤ X.GT :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT

theorem GT_eq_K_sup_QT : X.GT = X.K ⊔ X.QT ∧ X.QT = X.GT ⊓ X.S := by
  have h := X.pCoreOf_eq_inf_edgeSylow 0 (A := X.GT) X.K_le_GT
    (le_inf (X.GT_le_Gi 0) (X.GT_le_Gi 1))
  rw [X.edgeSylow_zero] at h
  exact ⟨h.2.symm, h.1⟩

theorem QT_fixes_vert (i : ℤ) {q : G} (hq : q ∈ X.QT) : q • X.vert i = X.vert i :=
  (Fan86.mem_fixSet.mp (X.QT_le_GT hq)) (X.vert i) ⟨i, rfl⟩

theorem QT_le_Q (i : ℤ) : X.QT ≤ X.Q i := by
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  refine le_pCoreOf_of_isPGroup_fixes_two X.hyp (P := X.QT) (pCoreOf_isPGroup' X.GT)
    ((X.QT_le_GT).trans (X.GT_le_Gi i)) hleft (X.adj i) hne ?_ ?_
  · intro q hq
    exact X.QT_fixes_vert (i - 1) hq
  · intro q hq
    exact X.QT_fixes_vert (i + 1) hq

theorem tau_mem_normalizer_GT : X.τ ∈ Subgroup.normalizer (X.GT : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hset : X.τ • (Set.range X.vert) = Set.range X.vert := by
    ext v
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i + 2, by simpa using (X.zpow_smul_vert 1 i).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨X.vert (j - 2), ⟨j - 2, rfl⟩, ?_⟩
      simpa [show j - 2 + 2 * (1 : ℤ) = j by ring] using X.zpow_smul_vert 1 (j - 2)
  change conjSub X.τ (fixSet G (Set.range X.vert)) = fixSet G (Set.range X.vert)
  rw [conjSub_fixSet, hset]

theorem tau_mem_normalizer_QT : X.τ ∈ Subgroup.normalizer (X.QT : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro q
  have hGT : conjSub X.τ X.GT = X.GT := by
    have h := X.tau_mem_normalizer_GT
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    exact h
  have hconj : conjSub X.τ X.QT = X.QT := by
    unfold Setup.QT
    rw [← pCoreOf_conjSub, hGT]
  have h := (mem_conjSub (g := X.τ) (x := q) (H := X.QT))
  rw [hconj] at h
  exact h

theorem K_le_normalizer_QT : X.K ≤ Subgroup.normalizer (X.QT : Set G) :=
  X.K_le_GT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT)

theorem QT_le_stabilizer_smul_vert (i : ℤ) {g : G}
    (hg : g ∈ Subgroup.normalizer (X.QT : Set G)) :
    X.QT ≤ MulAction.stabilizer G (g • X.vert i) := by
  intro q hq
  rw [MulAction.mem_stabilizer_iff]
  have hconj : g⁻¹ * q * g ∈ X.QT :=
    (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
  have hfix : (g⁻¹ * q * g) • X.vert i = X.vert i :=
    X.QT_fixes_vert i hconj
  calc q • (g • X.vert i) = (q * g) • X.vert i := (mul_smul q g _).symm
    _ = (g * (g⁻¹ * q * g)) • X.vert i := by
        rw [show q * g = g * (g⁻¹ * q * g) by group]
    _ = g • ((g⁻¹ * q * g) • X.vert i) := mul_smul g _ _
    _ = g • X.vert i := by rw [hfix]

theorem kernelOnNeighbors_le_edgeStab (i : ℤ) :
    kernelOnNeighbors Γ G (X.vert i) ≤ X.Gi i ⊓ X.Gi (i + 1) := by
  refine le_inf (kernelOnNeighbors_le _) ?_
  intro c hc
  exact MulAction.mem_stabilizer_iff.mpr
    ((mem_kernelOnNeighbors.mp hc).2 (X.vert (i + 1)) (X.adj i))

theorem kernelOnNeighbors_le_normalizer (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (kernelOnNeighbors Γ G (X.vert i) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (kernelOnNeighbors_le _)).mp
    (kernelOnNeighbors_normal X.hyp (X.vert i))

theorem kernelOnNeighbors_subgroupOf_edgeStab_normal (i : ℤ) :
    ((kernelOnNeighbors Γ G (X.vert i)).subgroupOf (X.Gi i ⊓ X.Gi (i + 1))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (inf_le_left.trans (X.kernelOnNeighbors_le_normalizer i))

theorem edgeSylow_subgroupOf_normal (i : ℤ) :
    ((X.edgeSylow i).subgroupOf (X.Gi i ⊓ X.Gi (i + 1))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i ⊓ X.Gi (i + 1)))

theorem kernelOnNeighbors_inf_edgeSylow (i : ℤ) :
    kernelOnNeighbors Γ G (X.vert i) ⊓ X.edgeSylow i = X.Q i := by
  have hleft : Γ.Adj (X.vert i) (X.vert (i - 1)) := by
    have h := (X.adj (i - 1)).symm
    rwa [show i - 1 + 1 = i by omega] at h
  have hne : X.vert (i - 1) ≠ X.vert (i + 1) := by
    intro h
    have := X.vert_injective h
    omega
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxC, hxS⟩ := Subgroup.mem_inf.mp hx
    have hxGi : x ∈ X.Gi i := kernelOnNeighbors_le _ hxC
    have hx2 : ∃ m : ℕ, x ^ 2 ^ m = 1 := by
      have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
        (X.isPGroup_edgeSylow i).to_le (Subgroup.zpowers_le.mpr hxS)
      obtain ⟨m, hm⟩ := hzp ⟨x, Subgroup.mem_zpowers x⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact mem_pCoreOf_of_fixes_two X.hyp hxGi hx2 hleft (X.adj i) hne
      ((mem_kernelOnNeighbors.mp hxC).2 _ hleft)
      ((mem_kernelOnNeighbors.mp hxC).2 _ (X.adj i))
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, X.Q_le_edgeSylow_left i hx⟩
    exact mem_kernelOnNeighbors.mpr
      ⟨X.Q_le_Gi i hx, fun a ha => X.Q_fixes_neighbors_vert i a ha x hx⟩

theorem two_not_dvd_relIndex_Q_kernelOnNeighbors (i : ℤ) :
    ¬ 2 ∣ (X.Q i).relIndex (kernelOnNeighbors Γ G (X.vert i)) := by
  classical
  set C := kernelOnNeighbors Γ G (X.vert i) with hCdef
  set H := X.Gi i ⊓ X.Gi (i + 1) with hHdef
  have hCH : C ≤ H := X.kernelOnNeighbors_le_edgeStab i
  have hSH : X.edgeSylow i ≤ H := (X.isSylowTwoOf_edgeSylow i).1
  have hCinfS : X.edgeSylow i ⊓ C = X.Q i := by
    rw [inf_comm, X.kernelOnNeighbors_inf_edgeSylow]
  have hQeq : (X.Q i).relIndex C = (X.edgeSylow i).relIndex C := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := X.edgeSylow i) (K := C) (L := C)
    rw [inf_idem, Subgroup.relIndex_self, mul_one] at h
    rw [h, hCinfS]
  have hSeq : (X.edgeSylow i).relIndex C =
      (X.edgeSylow i).relIndex (C ⊔ X.edgeSylow i) := by
    haveI : ((X.edgeSylow i).subgroupOf H).Normal := X.edgeSylow_subgroupOf_normal i
    rw [← Subgroup.relIndex_subgroupOf (H := X.edgeSylow i) (K := C) (L := H) hCH,
      ← Subgroup.relIndex_subgroupOf (H := X.edgeSylow i) (K := C ⊔ X.edgeSylow i) (L := H)
        (sup_le hCH hSH),
      Subgroup.subgroupOf_sup hCH hSH]
    exact (Subgroup.relIndex_sup_right (H := C.subgroupOf H)
      (K := (X.edgeSylow i).subgroupOf H)).symm
  have hdvd : (X.Q i).relIndex C ∣ (X.edgeSylow i).relIndex H := by
    rw [hQeq, hSeq]
    exact ⟨_, (Subgroup.relIndex_mul_relIndex (H := X.edgeSylow i)
      (K := C ⊔ X.edgeSylow i) (L := H) le_sup_right (sup_le hCH hSH)).symm⟩
  exact fun h2 => (X.isSylowTwoOf_edgeSylow i).2.2 (h2.trans hdvd)

theorem kernel_le_Q_sup_K (i : ℤ) :
    kernelOnNeighbors Γ G (X.vert i) ≤ X.Q i ⊔ X.K := by
  classical
  set C := kernelOnNeighbors Γ G (X.vert i) with hCdef
  set H := X.Gi i ⊓ X.Gi (i + 1) with hHdef
  have hCH : C ≤ H := X.kernelOnNeighbors_le_edgeStab i
  have hQC : X.Q i ≤ C := by
    intro x hx
    exact mem_kernelOnNeighbors.mpr ⟨X.Q_le_Gi i hx,
      fun a ha => X.Q_fixes_neighbors_vert i a ha x hx⟩
  have hCinfS : X.edgeSylow i ⊓ C = X.Q i := by
    rw [inf_comm, X.kernelOnNeighbors_inf_edgeSylow]
  have hCnorm : X.Gi i ≤ Subgroup.normalizer (C : Set G) :=
    X.kernelOnNeighbors_le_normalizer i
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := inf_le_left.trans hCnorm
  have hSnorm : H ≤ Subgroup.normalizer (X.edgeSylow i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (X.isSylowTwoOf_edgeSylow i).1).mp
      (X.edgeSylow_subgroupOf_normal i)
  have hCHnorm : C ≤ Subgroup.normalizer (X.edgeSylow i : Set G) := hCH.trans hSnorm
  haveI : Finite ↥C := finite_of_le_stabilizer X.hyp (hCH.trans inf_le_left)
  have hQnormC : C ≤ Subgroup.normalizer (X.Q i : Set G) :=
    (hCH.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i))
  have hNnormal : ((X.Q i).subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQnormC
  have hcop : Nat.Coprime (Nat.card ↥((X.Q i).subgroupOf C)) ((X.Q i).subgroupOf C).index := by
    haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi i)
    have hcard : Nat.card ↥((X.Q i).subgroupOf C) = Nat.card ↥(X.Q i) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup' (X.Gi i))
    rw [show ((X.Q i).subgroupOf C).index = (X.Q i).relIndex C from rfl, hcard, hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (X.two_not_dvd_relIndex_Q_kernelOnNeighbors i))
  obtain ⟨L', hL'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set L : Subgroup G := L'.map C.subtype with hL
  have hLC : L ≤ C := Subgroup.map_subtype_le L'
  have hLcard : Nat.card ↥L = Nat.card ↥L' :=
    Subgroup.card_map_of_injective (K := L') C.subtype_injective
  have hLodd : Odd (Nat.card ↥L) := by
    have hodd : Odd (((X.Q i).subgroupOf C).index) := by
      rw [show ((X.Q i).subgroupOf C).index = (X.Q i).relIndex C from rfl]
      exact Nat.not_even_iff_odd.mp (fun h => X.two_not_dvd_relIndex_Q_kernelOnNeighbors i
        (by simpa [even_iff_two_dvd] using h))
    rw [hLcard, show Nat.card ↥L' = ((X.Q i).subgroupOf C).index from hL'.card_right]
    exact hodd
  have hLsup : X.Q i ⊔ L = C := by
    refine le_antisymm (sup_le hQC hLC) ?_
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥C) ∈ ((X.Q i).subgroupOf C) ⊔ L' := by
      rw [hL'.sup_eq_top]; exact Subgroup.mem_top _
    haveI : ((X.Q i).subgroupOf C).Normal := hNnormal
    obtain ⟨n, hn, l, hl, hnl⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    rw [Subgroup.mem_subgroupOf] at hn
    have hnlG : (n : G) * (l : G) = x := by
      simpa using congrArg Subtype.val hnl
    rw [← hnlG]
    exact Subgroup.mul_mem_sup hn (Subgroup.mem_map_of_mem C.subtype hl)
  have hLinf : X.Q i ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxL⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hxL
    have hlN : l ∈ (X.Q i).subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      rw [show (l : G) = x from hlx]
      exact hxQ
    have hbot : l ∈ (⊥ : Subgroup ↥C) := by
      rw [← disjoint_iff.mp hL'.disjoint]
      exact Subgroup.mem_inf.mpr ⟨hlN, hl⟩
    rw [Subgroup.mem_bot] at hbot
    rw [← hlx, hbot]
    simp
  have hSinfL : X.edgeSylow i ⊓ L = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup hLodd (X.isPGroup_edgeSylow i)
  set F := X.edgeSylow i ⊔ L with hF
  have hSF : X.edgeSylow i ≤ F := le_sup_left
  have hLF : L ≤ F := le_sup_right
  have hFH : F ≤ H := sup_le (X.isSylowTwoOf_edgeSylow i).1 (hLC.trans hCH)
  haveI : Finite ↥F := finite_of_le_stabilizer X.hyp (hFH.trans inf_le_left)
  have hSylowF : IsSylowTwoOf (X.edgeSylow i) F :=
    F7.isSylowTwoOf_mono_right (X.isSylowTwoOf_edgeSylow i) hSF hFH
  have hSnormF : ((X.edgeSylow i).subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hFH.trans hSnorm)
  set K1 := F ⊓ X.K with hK1
  have hK1F : K1 ≤ F := inf_le_left
  have hK1K : K1 ≤ X.K := inf_le_right
  have hK1sup : X.edgeSylow i ⊔ K1 = F := by
    have hKH : X.K ≤ H := le_inf (X.K_le_Gi i) (X.K_le_Gi (i + 1))
    have hmul : (↑(X.K ⊔ X.edgeSylow i) : Set G) = X.K * X.edgeSylow i :=
      Subgroup.coe_mul_of_left_le_normalizer_right X.K (X.edgeSylow i)
        (hKH.trans hSnorm)
    rw [X.K_sup_edgeSylow i] at hmul
    refine le_antisymm (sup_le hSF inf_le_left) ?_
    intro x hx
    have hxmul : x ∈ (X.K : Set G) * (X.edgeSylow i : Set G) := by
      rw [← hmul]; exact hFH hx
    obtain ⟨k, hk, s, hs, hks⟩ := hxmul
    have hs' : k * s * k⁻¹ ∈ X.edgeSylow i :=
      (Subgroup.mem_normalizer_iff.mp (hSnorm (hKH hk)) s).mp hs
    have hkF : k ∈ F := by
      have hk_eq : k = (k * s * k⁻¹)⁻¹ * x := by rw [← hks]; group
      rw [hk_eq]
      exact F.mul_mem (F.inv_mem (hSF hs')) hx
    have hx_eq : x = (k * s * k⁻¹) * k := by rw [← hks]; group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hs' (Subgroup.mem_inf.mpr ⟨hkF, hk⟩)
  have hK1inf : X.edgeSylow i ⊓ K1 = ⊥ := by
    rw [hK1, ← inf_assoc, inf_eq_left.mpr hSF, inf_comm, X.K_inf_edgeSylow i]
  obtain ⟨n, hnS, hnK⟩ := exists_conj_eq_of_complement (F := F) (N := X.edgeSylow i)
    (H := L) (K := K1) hSF hSnormF hSylowF hLF hK1F hF.symm hK1sup hSinfL hK1inf
  have hSC : ⁅X.edgeSylow i, C⁆ ≤ X.Q i := by
    have h1 : X.edgeSylow i ≤ Subgroup.normalizer (C : Set G) :=
      ((X.isSylowTwoOf_edgeSylow i).1).trans hCnormH
    calc ⁅X.edgeSylow i, C⁆ ≤ X.edgeSylow i ⊓ C := F7.commutator_le_inf_of_normalizes h1 hCHnorm
      _ = X.Q i := hCinfS
  have hnH : n ∈ H := ((X.isSylowTwoOf_edgeSylow i).1) hnS
  have hL_le : L ≤ X.Q i ⊔ X.K := by
    intro l hl
    have hlF : l ∈ F := hLF hl
    have hkK1 : n⁻¹ * l * n ∈ K1 := by
      rw [hnK, mem_conjSub]
      convert hl using 2
      group
    have hkK : n⁻¹ * l * n ∈ X.K := hK1K hkK1
    have hkC : n⁻¹ * l * n ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp (hCnormH hnH) l).mp (hLC hl)
    have hcomm : ⁅n, n⁻¹ * l * n⁆ ∈ X.Q i :=
      (Subgroup.commutator_le.mp hSC) n hnS (n⁻¹ * l * n) hkC
    have hl_eq : l = ⁅n, n⁻¹ * l * n⁆ * (n⁻¹ * l * n) := by
      rw [commutatorElement_def]; group
    rw [hl_eq]
    exact Subgroup.mul_mem_sup hcomm hkK
  rw [← hLsup]
  exact sup_le le_sup_left hL_le

theorem inf_sup_Q_K_eq (i : ℤ) {M : Subgroup G} (hKM : X.K ≤ M) :
    M ⊓ (X.Q i ⊔ X.K) = (M ⊓ X.Q i) ⊔ X.K := by
  refine le_antisymm ?_ (sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
    (le_inf hKM le_sup_right))
  intro x hx
  obtain ⟨hxM, hxQK⟩ := Subgroup.mem_inf.mp hx
  have hmul : (↑(X.Q i ⊔ X.K) : Set G) = (X.Q i : Set G) * (X.K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (X.Q i) X.K
      ((X.K_le_Gi i).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)))
  have hxmul : x ∈ (X.Q i : Set G) * (X.K : Set G) := by
    rw [← hmul]
    exact hxQK
  obtain ⟨q, hq, k, hk, hqk⟩ := hxmul
  have hqM : q ∈ M := by
    have hq_eq : q = x * k⁻¹ := by rw [← hqk]; group
    rw [hq_eq]
    exact M.mul_mem hxM (M.inv_mem (hKM hk))
  rw [← hqk]
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hqM, hq⟩) hk

theorem edgeStab_eq_K_sup (i : ℤ) {w : V} (hw : Γ.Adj (X.vert i) w)
    (hKw : ∀ k ∈ X.K, k • w = w) :
    X.K ⊔ pCoreOf 2 (X.Gi i ⊓ MulAction.stabilizer G w) =
      X.Gi i ⊓ MulAction.stabilizer G w := by
  classical
  set E := X.Gi i ⊓ MulAction.stabilizer G w with hE
  set Sw := pCoreOf 2 E with hSw
  have hKE : X.K ≤ E :=
    le_inf (X.K_le_Gi i) (fun k hk => MulAction.mem_stabilizer_iff.mpr (hKw k hk))
  have hSylowE : IsSylowTwoOf Sw E := isSylowTwoOf_pCoreOf_edgeStab X.hyp hw
  haveI : Finite ↥E := finite_of_le_stabilizer X.hyp (H := E) inf_le_left
  haveI : Finite ↥Sw := Finite.of_injective
    (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 E)) (Subgroup.inclusion_injective _)
  have hKinf : X.K ⊓ Sw = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (A := X.K) (B := Sw) X.odd_card_K hSylowE.2.1
  have hcard : Nat.card ↥E = Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) ∧
      Nat.card ↥Sw = Nat.card ↥X.S := by
    obtain ⟨g, -, hor⟩ :=
      X.hyp.edgeTrans (X.vert i) w (X.vert 0) (X.vert 1) hw (X.adj 0)
    have key : ∀ {a b : V} (_h1 : g • X.vert i = a) (_h2 : g • w = b),
        Nat.card ↥E = Nat.card ↥(MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) ∧
        Nat.card ↥Sw =
          Nat.card ↥(pCoreOf 2 (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)) := by
      intro a b h1 h2
      have hGa : MulAction.stabilizer G a = conjSub g (X.Gi i) := by
        rw [Setup.Gi, ← h1, stabilizer_smul_eq_conjSub]
      have hGb : MulAction.stabilizer G b = conjSub g (MulAction.stabilizer G w) := by
        rw [← h2, stabilizer_smul_eq_conjSub]
      have hconj : conjSub g E = MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
        rw [hE, conjSub_inf, hGa, hGb]
      constructor
      · rw [← hconj]
        exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulEquiv.injective _)).symm
      · rw [hSw, ← hconj, pCoreOf_conjSub]
        exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulEquiv.injective _)).symm
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h := key (a := X.vert 0) (b := X.vert 1) h1 h2
      simpa only [Setup.Gi] using h
    · have h := key (a := X.vert 1) (b := X.vert 0) h1 h2
      simpa only [Setup.Gi, inf_comm] using h
  have hKcard : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) = Nat.card ↥X.K * Nat.card ↥X.S := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X.S X.K
      ((le_inf (X.K_le_Gi 0) (X.K_le_Gi 1)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1)))
      (disjoint_iff.mpr (by rw [inf_comm]; exact X.K_inf_edgeSylow 0))
    rw [sup_comm, ← X.edgeSylow_zero, X.K_sup_edgeSylow 0, mul_comm] at h
    exact h
  have hsup : Nat.card ↥(X.K ⊔ Sw) = Nat.card ↥X.K * Nat.card ↥Sw := by
    rw [sup_comm]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Sw X.K
      (hKE.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E))
      (disjoint_iff.mpr (by rw [inf_comm]; exact hKinf)), mul_comm]
  have hEq : X.K ⊔ Sw = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hKE (CFSG.LieType.BorelTits.pCoreOf_le 2 E)) ?_
    rw [hsup, hcard.1, hcard.2, ← hKcard]
  exact hEq

theorem K_inf_pCoreOf_edgeStab (i : ℤ) {w : V} (hw : Γ.Adj (X.vert i) w)
    (hKw : ∀ k ∈ X.K, k • w = w) :
    X.K ⊓ pCoreOf 2 (X.Gi i ⊓ MulAction.stabilizer G w) = ⊥ := by
  exact inf_eq_bot_of_odd_of_isPGroup (A := X.K)
    (B := pCoreOf 2 (X.Gi i ⊓ MulAction.stabilizer G w)) X.odd_card_K
    (isSylowTwoOf_pCoreOf_edgeStab X.hyp hw).2.1

theorem exists_normalizer_K_move {H : Subgroup G} (i : ℤ) (hKH : X.K ≤ H)
    (hH : H ≤ X.Gi i)
    (htr : ∀ a b : V, Γ.Adj (X.vert i) a → Γ.Adj (X.vert i) b → ∃ g ∈ H, g • a = b)
    {w w' : V} (hw : Γ.Adj (X.vert i) w) (hw' : Γ.Adj (X.vert i) w')
    (hKw : ∀ k ∈ X.K, k • w = w) (hKw' : ∀ k ∈ X.K, k • w' = w') :
    ∃ h ∈ H ⊓ Subgroup.normalizer (X.K : Set G), h • w' = w := by
  classical
  obtain ⟨g, hgH, hgw⟩ := htr w' w hw' hw
  set E := X.Gi i ⊓ MulAction.stabilizer G w with hE
  set Sw := pCoreOf 2 E with hSw
  set F := H ⊓ MulAction.stabilizer G w with hF
  have hFE : F ≤ E := le_inf (inf_le_left.trans hH) inf_le_right
  have hK_F : X.K ≤ F := le_inf hKH (fun k hk => MulAction.mem_stabilizer_iff.mpr (hKw k hk))
  have hEsup : X.K ⊔ Sw = E := X.edgeStab_eq_K_sup i hw hKw
  have hEinf : X.K ⊓ Sw = ⊥ := X.K_inf_pCoreOf_edgeStab i hw hKw
  have hSwE : Sw ≤ E := CFSG.LieType.BorelTits.pCoreOf_le 2 E
  haveI : Finite ↥E := finite_of_le_stabilizer X.hyp (H := E) inf_le_left
  haveI : Finite ↥Sw := Finite.of_injective (Subgroup.inclusion hSwE)
    (Subgroup.inclusion_injective _)
  haveI : Finite ↥F := finite_of_le_stabilizer X.hyp (H := F) (inf_le_left.trans hH)
  have hSF_le : F ⊓ Sw ≤ F := inf_le_left
  have hSF_normF : F ≤ Subgroup.normalizer ((F ⊓ Sw : Subgroup G) : Set G) :=
    F7.le_normalizer_inf Subgroup.le_normalizer
      (hFE.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E))

  have hFsup : X.K ⊔ (F ⊓ Sw) = F := by
    refine le_antisymm (sup_le hK_F inf_le_left) ?_
    intro x hx
    have hxE : x ∈ X.K ⊔ Sw := by rw [hEsup]; exact hFE hx
    have hmul : (↑(X.K ⊔ Sw) : Set G) = (X.K : Set G) * (Sw : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right X.K Sw
        (hK_F.trans (hFE.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)))
    have hxmul : x ∈ (X.K : Set G) * (Sw : Set G) := by rw [← hmul]; exact hxE
    obtain ⟨k, hk, q, hq, hkq⟩ := hxmul
    have hkF : k ∈ F := hK_F hk
    have hqF : q ∈ F := by
      have hq_eq : q = k⁻¹ * x := by rw [← hkq]; group
      rw [hq_eq]
      exact F.mul_mem (F.inv_mem hkF) hx
    rw [← hkq]
    exact Subgroup.mul_mem_sup hk (Subgroup.mem_inf.mpr ⟨hqF, hq⟩)
  have hFinf : X.K ⊓ (F ⊓ Sw) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hK_F, hEinf]
  have hodd : ¬ 2 ∣ (F ⊓ Sw).relIndex F := by
    have hEq1 : (F ⊓ Sw).relIndex F = Sw.relIndex F := by
      have h := Subgroup.relIndex_inf_mul_relIndex (H := Sw) (K := F) (L := F)
      rw [inf_idem, Subgroup.relIndex_self, mul_one] at h
      simpa only [inf_comm] using h.symm
    have hEq2 : Sw.relIndex F = Sw.relIndex (F ⊔ Sw) := by
      haveI : (Sw.subgroupOf E).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)
      rw [← Subgroup.relIndex_subgroupOf (H := Sw) (K := F) (L := E) hFE,
        ← Subgroup.relIndex_subgroupOf (H := Sw) (K := F ⊔ Sw) (L := E) (sup_le hFE hSwE),
        Subgroup.subgroupOf_sup hFE hSwE]
      exact (Subgroup.relIndex_sup_right (H := F.subgroupOf E)
        (K := Sw.subgroupOf E)).symm
    rw [hEq1, hEq2]
    exact fun h2 => (isSylowTwoOf_pCoreOf_edgeStab X.hyp hw).2.2 (h2.trans
      ⟨_, (Subgroup.relIndex_mul_relIndex (H := Sw) (K := F ⊔ Sw) (L := E)
        le_sup_right (sup_le hFE hSwE)).symm⟩)
  haveI : Finite ↥(F ⊓ Sw) :=
    Finite.of_injective (Subgroup.inclusion hSF_le) (Subgroup.inclusion_injective _)
  have hSylowF : IsSylowTwoOf (F ⊓ Sw) F :=
    F7.isSylowTwoOf_of_relIndex hSF_le
      ((isSylowTwoOf_pCoreOf_edgeStab X.hyp hw).2.1.to_le inf_le_right) hodd
  have hSF_norm : ((F ⊓ Sw).subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hSF_normF
  have hgwinv : g⁻¹ • w = w' := by
    have h : w' = g⁻¹ • w := by
      have := congrArg (fun v => g⁻¹ • v) hgw
      simpa using this
    exact h.symm
  have hKgF : conjSub g X.K ≤ F := by
    refine le_inf ?_ ?_
    · rintro x ⟨k, hk, rfl⟩
      exact H.mul_mem (H.mul_mem hgH (hKH hk)) (H.inv_mem hgH)
    · rintro x ⟨k, hk, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      calc (g * k * g⁻¹) • w = g • (k • (g⁻¹ • w)) := by simp only [mul_smul]
        _ = g • (k • w') := by rw [hgwinv]
        _ = g • w' := by rw [hKw' k hk]
        _ = w := hgw
  haveI : Finite ↥(conjSub g X.K) :=
    Finite.of_injective (Subgroup.inclusion hKgF) (Subgroup.inclusion_injective _)
  have hKg_inf : conjSub g X.K ⊓ (F ⊓ Sw) = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (A := conjSub g X.K) (B := F ⊓ Sw)
      (by rw [card_conjSub]; exact X.odd_card_K)
      ((isSylowTwoOf_pCoreOf_edgeStab X.hyp hw).2.1.to_le inf_le_right)
  have hKg_sup : conjSub g X.K ⊔ (F ⊓ Sw) = F := by
    have h1 : Nat.card ↥F = Nat.card ↥X.K * Nat.card ↥(F ⊓ Sw) := by
      have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (F ⊓ Sw) X.K (hK_F.trans hSF_normF)
        (disjoint_iff.mpr (by rw [inf_comm]; exact hFinf))
      rw [sup_comm, hFsup, mul_comm] at h
      exact h
    have h2 : Nat.card ↥(conjSub g X.K ⊔ (F ⊓ Sw)) =
        Nat.card ↥X.K * Nat.card ↥(F ⊓ Sw) := by
      have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (F ⊓ Sw) (conjSub g X.K) (hKgF.trans hSF_normF)
        (disjoint_iff.mpr (by rw [inf_comm]; exact hKg_inf))
      rw [sup_comm, card_conjSub, mul_comm] at h
      exact h
    refine Subgroup.eq_of_le_of_card_ge (sup_le hKgF inf_le_left) ?_
    rw [h2, ← h1]
  obtain ⟨c, hcSF, hc⟩ := exists_conj_eq_of_complement (F := F) (N := F ⊓ Sw)
    hSF_le hSF_norm hSylowF hK_F hKgF (by rw [sup_comm]; exact hFsup)
    (by rw [sup_comm]; exact hKg_sup) (by rw [inf_comm]; exact hFinf)
    (by rw [inf_comm]; exact hKg_inf)
  have hcF : c ∈ F := (inf_le_left : F ⊓ Sw ≤ F) hcSF
  have hcH : c ∈ H := (inf_le_left : F ≤ H) hcF
  have hcw : c • w = w :=
    MulAction.mem_stabilizer_iff.mp ((inf_le_right : F ≤ MulAction.stabilizer G w) hcF)
  refine ⟨c * g, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨H.mul_mem hcH hgH, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub (c * g) X.K = X.K
    rw [conjSub_mul, hc, conjSub_inv_conjSub]
  · calc (c * g) • w' = c • (g • w') := mul_smul c g w'
      _ = c • w := by rw [hgw]
      _ = w := hcw

@[expose] def IsMaxReg (a b : ℤ) : Prop :=
  a < b ∧ X.LeftTransAt a b ∧ X.RightTransAt a b ∧
    X.arcStab a (b + 1) = X.GT ∧ X.arcStab (a - 1) b = X.GT

@[expose] def IsInclMaxReg (a b : ℤ) : Prop :=
  a < b ∧ X.LeftTransAt a b ∧ X.RightTransAt a b ∧
    ∀ c d, c ≤ a → b ≤ d → (c, d) ≠ (a, b) →
      ¬ (X.LeftTransAt c d ∧ X.RightTransAt c d)

theorem le_GT_of_fixSet_eq_univ {U : Subgroup G} (h : X.fixSet U = Set.univ) :
    U ≤ X.GT := by
  intro u hu
  rw [Setup.GT, Fan86.mem_fixSet]
  rintro v ⟨i, rfl⟩
  have hi : i ∈ X.fixSet U := by rw [h]; exact Set.mem_univ i
  exact hi u hu

theorem le_arcStab_of_fixSet {U : Subgroup G} {a b : ℤ} (h : Set.Icc a b ⊆ X.fixSet U) :
    U ≤ X.arcStab a b := by
  intro u hu
  unfold Setup.arcStab
  rw [Fan86.mem_fixSet]
  rintro v ⟨i, hi, rfl⟩
  exact h hi u hu

theorem isMaxReg_of_isInclMaxReg {a b : ℤ} (h : X.IsInclMaxReg a b) : X.IsMaxReg a b := by
  classical
  have hab : a < b := h.1
  have hleft : X.LeftTransAt a b := h.2.1
  have hright : X.RightTransAt a b := h.2.2.1
  have hright_ext : X.arcStab a (b + 1) = X.GT := by
    set U := X.arcStab a (b + 1) with hU
    set P := pCoreOf 2 U with hP
    have hKU : X.K ≤ U := X.K_le_GT.trans (X.GT_le_arcStab a (b + 1))
    have hUU : U ≤ X.Gi b ⊓ X.Gi (b + 1) :=
      le_inf (X.arcStab_le_Gi_of_between (by omega) (by omega))
        (X.arcStab_le_Gi_of_between (by omega) le_rfl)
    obtain ⟨-, hUdecomp⟩ := X.pCoreOf_eq_inf_edgeSylow b hKU hUU
    have hPleGT : P ≤ X.GT := by
      rcases fixSet_trichotomy X.hyp.isTree X.hyp.adj_smul X.hyp.finite_stab X.toTrack P with
        huniv | hempty | ⟨c, d, hcd, hfix⟩
      · exact X.le_GT_of_fixSet_eq_univ huniv
      · exfalso
        have hb : b + 1 ∈ X.fixSet P := by
          intro p hp
          exact X.arcStab_le_Gi_of_between (by omega) le_rfl (hUdecomp ▸ Subgroup.mem_sup_right hp)
        rw [hempty] at hb
        simpa using hb
      · have hsub : Set.Icc a (b + 1) ⊆ X.fixSet P := by
          intro i hi
          rw [Set.mem_Icc] at hi
          intro p hp
          have hpU : p ∈ U := hUdecomp ▸ Subgroup.mem_sup_right hp
          exact X.arcStab_le_Gi_of_between hi.1 hi.2 hpU
        have hca : c ≤ a := by
          have := hsub (Set.mem_Icc.mpr ⟨le_rfl, by omega⟩)
          rw [hfix] at this
          exact (Set.mem_Icc.mp this).1
        have hdb : b + 1 ≤ d := by
          have := hsub (Set.mem_Icc.mpr ⟨by omega, le_rfl⟩)
          rw [hfix] at this
          exact (Set.mem_Icc.mp this).2
        have hc_d : c < d := by omega
        have harc : U = X.arcStab c d := by
          refine le_antisymm ?_ (X.arcStab_anti hca hdb)
          have hKcd : X.K ≤ X.arcStab c d := X.K_le_GT.trans (X.GT_le_arcStab c d)
          have hPcd : P ≤ X.arcStab c d := by
            refine X.le_arcStab_of_fixSet ?_
            intro i hi
            rw [hfix]
            exact hi
          rw [← hUdecomp]
          exact sup_le hKcd hPcd
        have hpcle : X.LeftTransAt c d := by
          by_contra htr
          have hPleQ : P ≤ X.Q c := by
            have h1 : pCoreOf 2 (X.arcStab c d) ≤ X.Q c :=
              X.pCoreOf_arcStab_le_Q_left c d hc_d htr
            rw [← harc] at h1
            simpa only [hP] using h1
          have hcm : c - 1 ∈ X.fixSet P := by
            intro p hp
            exact X.Q_fixes_neighbors_vert c _ (by
              have h := (X.adj (c - 1)).symm
              rwa [show c - 1 + 1 = c by omega] at h) p (hPleQ hp)
          rw [hfix] at hcm
          have := (Set.mem_Icc.mp hcm).1
          omega
        have hprcle : X.RightTransAt c d := by
          by_contra htr
          have hPleQ : P ≤ X.Q d := by
            have h1 : pCoreOf 2 (X.arcStab c d) ≤ X.Q d :=
              X.pCoreOf_arcStab_le_Q_right c d hc_d htr
            rw [← harc] at h1
            simpa only [hP] using h1
          have hdm : d + 1 ∈ X.fixSet P := by
            intro p hp
            exact X.Q_fixes_neighbors_vert d _ (X.adj d) p (hPleQ hp)
          rw [hfix] at hdm
          have := (Set.mem_Icc.mp hdm).2
          omega
        exact absurd ⟨hpcle, hprcle⟩ (h.2.2.2 c d hca (by omega) (by
          intro heq
          have : d = b := congrArg Prod.snd heq
          omega))
    have hUGT : U ≤ X.GT := by
      rw [← hUdecomp]
      exact sup_le X.K_le_GT hPleGT
    exact le_antisymm hUGT (X.GT_le_arcStab a (b + 1))
  have hleft_ext : X.arcStab (a - 1) b = X.GT := by
    set U := X.arcStab (a - 1) b with hU
    set P := pCoreOf 2 U with hP
    have hKU : X.K ≤ U := X.K_le_GT.trans (X.GT_le_arcStab (a - 1) b)
    have hUU : U ≤ X.Gi (a - 1) ⊓ X.Gi (a - 1 + 1) := by
      rw [show a - 1 + 1 = a by omega]
      exact le_inf (X.arcStab_le_Gi_of_between le_rfl (by omega))
        (X.arcStab_le_Gi_of_between (by omega) (by omega))
    obtain ⟨-, hUdecomp⟩ := X.pCoreOf_eq_inf_edgeSylow (a - 1) hKU hUU
    have hPleGT : P ≤ X.GT := by
      rcases fixSet_trichotomy X.hyp.isTree X.hyp.adj_smul X.hyp.finite_stab X.toTrack P with
        huniv | hempty | ⟨c, d, hcd, hfix⟩
      · exact X.le_GT_of_fixSet_eq_univ huniv
      · exfalso
        have ha : a - 1 ∈ X.fixSet P := by
          intro p hp
          exact X.arcStab_le_Gi_of_between le_rfl (by omega)
            (hUdecomp ▸ Subgroup.mem_sup_right hp)
        rw [hempty] at ha
        simpa using ha
      · have hsub : Set.Icc (a - 1) b ⊆ X.fixSet P := by
          intro i hi
          rw [Set.mem_Icc] at hi
          intro p hp
          have hpU : p ∈ U := hUdecomp ▸ Subgroup.mem_sup_right hp
          exact X.arcStab_le_Gi_of_between hi.1 hi.2 hpU
        have hca : c ≤ a - 1 := by
          have := hsub (Set.mem_Icc.mpr ⟨le_rfl, by omega⟩)
          rw [hfix] at this
          exact (Set.mem_Icc.mp this).1
        have hca' : c ≤ a := by omega
        have hdb : b ≤ d := by
          have := hsub (Set.mem_Icc.mpr ⟨by omega, le_rfl⟩)
          rw [hfix] at this
          exact (Set.mem_Icc.mp this).2
        have hc_d : c < d := by omega
        have harc : U = X.arcStab c d := by
          refine le_antisymm ?_ (X.arcStab_anti hca hdb)
          have hKcd : X.K ≤ X.arcStab c d := X.K_le_GT.trans (X.GT_le_arcStab c d)
          have hPcd : P ≤ X.arcStab c d := by
            refine X.le_arcStab_of_fixSet ?_
            intro i hi
            rw [hfix]
            exact hi
          rw [← hUdecomp]
          exact sup_le hKcd hPcd
        have hpcle : X.LeftTransAt c d := by
          by_contra htr
          have hPleQ : P ≤ X.Q c := by
            have h1 : pCoreOf 2 (X.arcStab c d) ≤ X.Q c :=
              X.pCoreOf_arcStab_le_Q_left c d hc_d htr
            rw [← harc] at h1
            simpa only [hP] using h1
          have hcm : c - 1 ∈ X.fixSet P := by
            intro p hp
            exact X.Q_fixes_neighbors_vert c _ (by
              have h := (X.adj (c - 1)).symm
              rwa [show c - 1 + 1 = c by omega] at h) p (hPleQ hp)
          rw [hfix] at hcm
          have := (Set.mem_Icc.mp hcm).1
          omega
        have hprcle : X.RightTransAt c d := by
          by_contra htr
          have hPleQ : P ≤ X.Q d := by
            have h1 : pCoreOf 2 (X.arcStab c d) ≤ X.Q d :=
              X.pCoreOf_arcStab_le_Q_right c d hc_d htr
            rw [← harc] at h1
            simpa only [hP] using h1
          have hdm : d + 1 ∈ X.fixSet P := by
            intro p hp
            exact X.Q_fixes_neighbors_vert d _ (X.adj d) p (hPleQ hp)
          rw [hfix] at hdm
          have := (Set.mem_Icc.mp hdm).2
          omega
        exact absurd ⟨hpcle, hprcle⟩ (h.2.2.2 c d hca' hdb (by
          intro heq
          have : c = a := congrArg Prod.fst heq
          omega))
    have hUGT : U ≤ X.GT := by
      rw [← hUdecomp]
      exact sup_le X.K_le_GT hPleGT
    exact le_antisymm hUGT (X.GT_le_arcStab (a - 1) b)
  exact ⟨hab, hleft, hright, hright_ext, hleft_ext⟩

theorem arcStab_le_normalizer_QT_of_isMaxReg {a b : ℤ} (h : X.IsMaxReg a b) :
    X.arcStab a b ≤ Subgroup.normalizer (X.QT : Set G) := by
  classical
  have hab : a < b := h.1
  set W := X.arcStab a b ⊓ kernelOnNeighbors Γ G (X.vert b) with hW
  have hker : X.Gi b ≤ Subgroup.normalizer (kernelOnNeighbors Γ G (X.vert b) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (kernelOnNeighbors_le _)).mp
      (kernelOnNeighbors_normal X.hyp (X.vert b))
  have hWnorm : X.arcStab a b ≤ Subgroup.normalizer (W : Set G) := by
    intro g hg
    have hgG : g ∈ X.Gi b := X.arcStab_le_Gi_right hab hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g W = W
    have hkc : conjSub g (kernelOnNeighbors Γ G (X.vert b)) =
        kernelOnNeighbors Γ G (X.vert b) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hker hgG)
    rw [hW, conjSub_inf, conjSub_eq_of_mem hg, hkc]
  have hW_le_GT : W ≤ X.GT := by
    intro w hw
    obtain ⟨hwA, hwK⟩ := Subgroup.mem_inf.mp hw
    rw [← h.2.2.2.1, X.arcStab_eq_inf (show a ≤ b + 1 by omega)]
    exact Subgroup.mem_inf.mpr ⟨X.arcStab_le_Gi_left hab hwA,
      MulAction.mem_stabilizer_iff.mpr ((mem_kernelOnNeighbors.mp hwK).2 _ (X.adj b))⟩
  have hGTnormW : X.GT ≤ Subgroup.normalizer (W : Set G) := (X.GT_le_arcStab a b).trans hWnorm
  have hQT_W : X.QT ≤ W := by
    refine le_inf (X.QT_le_GT.trans (X.GT_le_arcStab a b)) ?_
    intro q hq
    exact mem_kernelOnNeighbors.mpr
      ⟨X.Q_le_Gi b (X.QT_le_Q b hq),
        fun v hv => X.Q_fixes_neighbors_vert b v hv q (X.QT_le_Q b hq)⟩
  have hQT_eq : X.QT = pCoreOf 2 W := by
    refine le_antisymm ?_ ?_
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQT_W
        (hW_le_GT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT))
        (pCoreOf_isPGroup' X.GT)
    · have hPleGT : pCoreOf 2 W ≤ X.GT :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 W).trans hW_le_GT
      have hGTnormP : X.GT ≤ Subgroup.normalizer (pCoreOf 2 W : Set G) :=
        hGTnormW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPleGT hGTnormP
        (pCoreOf_isPGroup' W)
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub g X.QT = X.QT
  have hWconj : conjSub g W = W := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWnorm hg)
  rw [hQT_eq, ← pCoreOf_conjSub, hWconj]

theorem leftTransAt_add (m a c : ℤ) (h : X.LeftTransAt a c) :
    X.LeftTransAt (a + 2 * m) (c + 2 * m) := by
  intro x y hx hx1 hy hy1
  set x' : V := (X.τ ^ m)⁻¹ • x with hx'def
  set y' : V := (X.τ ^ m)⁻¹ • y with hy'def
  have hx'inv : (X.τ ^ m) • x' = x := by simp [hx'def]
  have hy'inv : (X.τ ^ m) • y' = y := by simp [hy'def]
  have hxadj : Γ.Adj (X.vert a) x' := by
    have h1 : Γ.Adj ((X.τ ^ m) • X.vert a) ((X.τ ^ m) • x') := by
      rw [hx'inv]
      rwa [X.zpow_smul_vert]
    exact (X.hyp.adj_smul (X.τ ^ m) (X.vert a) x').1 h1
  have hyadj : Γ.Adj (X.vert a) y' := by
    have h1 : Γ.Adj ((X.τ ^ m) • X.vert a) ((X.τ ^ m) • y') := by
      rw [hy'inv]
      rwa [X.zpow_smul_vert]
    exact (X.hyp.adj_smul (X.τ ^ m) (X.vert a) y').1 h1
  have hx1' : x' ≠ X.vert (a + 1) := by
    intro hxe
    apply hx1
    have h2 : (X.τ ^ m) • x' = (X.τ ^ m) • X.vert (a + 1) := by rw [hxe]
    rw [hx'inv, X.zpow_smul_vert] at h2
    rw [h2]
    congr 1
    ring
  have hy1' : y' ≠ X.vert (a + 1) := by
    intro hye
    apply hy1
    have h2 : (X.τ ^ m) • y' = (X.τ ^ m) • X.vert (a + 1) := by rw [hye]
    rw [hy'inv, X.zpow_smul_vert] at h2
    rw [h2]
    congr 1
    ring
  obtain ⟨g, hg, hgxy⟩ := h x' y' hxadj hx1' hyadj hy1'
  refine ⟨(X.τ ^ m) * g * (X.τ ^ m)⁻¹, ?_, ?_⟩
  · have h1 : conjSub (X.τ ^ m) (X.arcStab a c) = X.arcStab (a + 2 * m) (c + 2 * m) :=
      (X.arcStab_add m a c).symm
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hg
  · calc ((X.τ ^ m) * g * (X.τ ^ m)⁻¹) • x
        = (X.τ ^ m) • (g • ((X.τ ^ m)⁻¹ • x)) := by simp only [mul_smul]
      _ = (X.τ ^ m) • (g • x') := by rw [hx'def]
      _ = (X.τ ^ m) • y' := by rw [hgxy]
      _ = y := hy'inv

theorem rightTransAt_add (m a c : ℤ) (h : X.RightTransAt a c) :
    X.RightTransAt (a + 2 * m) (c + 2 * m) := by
  intro x y hx hx1 hy hy1
  set x' : V := (X.τ ^ m)⁻¹ • x with hx'def
  set y' : V := (X.τ ^ m)⁻¹ • y with hy'def
  have hx'inv : (X.τ ^ m) • x' = x := by simp [hx'def]
  have hy'inv : (X.τ ^ m) • y' = y := by simp [hy'def]
  have hxadj : Γ.Adj (X.vert c) x' := by
    have h1 : Γ.Adj ((X.τ ^ m) • X.vert c) ((X.τ ^ m) • x') := by
      rw [hx'inv]
      rwa [X.zpow_smul_vert]
    exact (X.hyp.adj_smul (X.τ ^ m) (X.vert c) x').1 h1
  have hyadj : Γ.Adj (X.vert c) y' := by
    have h1 : Γ.Adj ((X.τ ^ m) • X.vert c) ((X.τ ^ m) • y') := by
      rw [hy'inv]
      rwa [X.zpow_smul_vert]
    exact (X.hyp.adj_smul (X.τ ^ m) (X.vert c) y').1 h1
  have hx1' : x' ≠ X.vert (c - 1) := by
    intro hxe
    apply hx1
    have h2 : (X.τ ^ m) • x' = (X.τ ^ m) • X.vert (c - 1) := by rw [hxe]
    rw [hx'inv, X.zpow_smul_vert] at h2
    rw [h2]
    congr 1
    ring
  have hy1' : y' ≠ X.vert (c - 1) := by
    intro hye
    apply hy1
    have h2 : (X.τ ^ m) • y' = (X.τ ^ m) • X.vert (c - 1) := by rw [hye]
    rw [hy'inv, X.zpow_smul_vert] at h2
    rw [h2]
    congr 1
    ring
  obtain ⟨g, hg, hgxy⟩ := h x' y' hxadj hx1' hyadj hy1'
  refine ⟨(X.τ ^ m) * g * (X.τ ^ m)⁻¹, ?_, ?_⟩
  · have h1 : conjSub (X.τ ^ m) (X.arcStab a c) = X.arcStab (a + 2 * m) (c + 2 * m) :=
      (X.arcStab_add m a c).symm
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hg
  · calc ((X.τ ^ m) * g * (X.τ ^ m)⁻¹) • x
        = (X.τ ^ m) • (g • ((X.τ ^ m)⁻¹ • x)) := by simp only [mul_smul]
      _ = (X.τ ^ m) • (g • x') := by rw [hx'def]
      _ = (X.τ ^ m) • y' := by rw [hgxy]
      _ = y := hy'inv

theorem even_of_even_dist (i : ℤ) (h : Even (Γ.dist (X.vert 0) (X.vert i))) : Even i := by
  rcases le_total 0 i with hi | hi
  · have hd : Γ.dist (X.vert 0) (X.vert i) = i.toNat := by
      have h := Line.dist_eq X.hyp.isTree X.line (i := (0 : ℤ)) (j := i) hi
      simpa using h
    rw [hd] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨(k : ℤ), ?_⟩
    have : i = (i.toNat : ℤ) := (Int.toNat_of_nonneg hi).symm
    omega
  · have hd : Γ.dist (X.vert 0) (X.vert i) = (-i).toNat := by
      have h1 : Γ.dist (X.vert i) (X.vert 0) = (0 - i).toNat :=
        Line.dist_eq X.hyp.isTree X.line (i := i) (j := 0) (by omega)
      rw [dist_comm] at h1
      simpa using h1
    rw [hd] at h
    obtain ⟨k, hk⟩ := h
    have h2 : Even ((-i).toNat : ℤ) := ⟨(k : ℤ), by omega⟩
    rw [Int.toNat_of_nonneg (by omega)] at h2
    exact even_neg.mp h2

theorem arcStab_ne_GT_of_rightTransAt {m r : ℤ} (hmr : m < r) (h : X.RightTransAt m r) :
    X.arcStab m r ≠ X.GT := by
  intro hEq
  have hleft : Γ.Adj (X.vert r) (X.vert (r - 1)) := by
    have h := (X.adj (r - 1)).symm
    rwa [show r - 1 + 1 = r by omega] at h
  have hne : X.vert (r + 1) ≠ X.vert (r - 1) := by
    intro h
    have := X.vert_injective h
    omega
  have hD : (Γ.neighborSet (X.vert r) \ {X.vert (r - 1)}).ncard = 2 ^ X.n r :=
    ncard_neighborSet_diff X.hyp hleft
  have h2 : 1 < (Γ.neighborSet (X.vert r) \ {X.vert (r - 1)}).ncard := by
    rw [hD]
    have hn : 1 ≤ X.n r := (X.hyp.valency (X.vert r)).1
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ X.n r := Nat.pow_le_pow_right (by norm_num) hn
  have hmemD : X.vert (r + 1) ∈ Γ.neighborSet (X.vert r) \ {X.vert (r - 1)} := by
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborSet]; exact X.adj r
    · simp only [Set.mem_singleton_iff]; exact hne
  obtain ⟨v, hvD, hvne⟩ := Set.exists_ne_of_one_lt_ncard h2 (X.vert (r + 1))
  obtain ⟨g, hg, hgv⟩ := h (X.vert (r + 1)) v (X.adj r) hne hvD.1 hvD.2
  have hgGT : g ∈ X.GT := hEq ▸ hg
  have hfix : g • X.vert (r + 1) = X.vert (r + 1) :=
    (Fan86.mem_fixSet.mp hgGT) (X.vert (r + 1)) ⟨r + 1, rfl⟩
  exact hvne (hgv.symm.trans hfix)

theorem exists_isMaxReg (hs : IsSingularity Γ G s) (hodd : Odd s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ∃ m : ℕ, s - 1 ≤ 2 * m ∧ X.IsMaxReg 0 (2 * m) := by
  classical
  have hs1 : 1 ≤ s := hs.1
  have hs3 : 3 ≤ s := by
    have hsne : s ≠ 1 := by
      rintro rfl
      obtain ⟨P, hP⟩ := hs.2.2
      exact hP (X.hyp.regular_of_length_one P)
    obtain ⟨k, hk⟩ := hodd
    omega
  let f : ℕ → ℕ := fun m => Nat.card ↥(X.arcStab (-(m : ℤ)) (m : ℤ))
  have hfanti : ∀ m, f (m + 1) ≤ f m := by
    intro m
    haveI : Finite ↥(X.arcStab (-(((m + 1 : ℕ)) : ℤ)) (((m + 1 : ℕ)) : ℤ)) :=
      finite_of_le_stabilizer X.hyp (H := X.arcStab (-(((m + 1 : ℕ)) : ℤ)) (((m + 1 : ℕ)) : ℤ))
        (X.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    haveI : Finite ↥(X.arcStab (-(m : ℤ)) (m : ℤ)) :=
      finite_of_le_stabilizer X.hyp (H := X.arcStab (-(m : ℤ)) (m : ℤ))
        (X.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    exact Subgroup.card_le_of_le (X.arcStab_anti (by omega) (by omega))
  have hex : ∃ n, ∃ m, f m = n := ⟨f 0, 0, rfl⟩
  set n₀ := Nat.find hex with hn₀def
  obtain ⟨m₀, hm₀⟩ := hn₀def.symm ▸ Nat.find_spec hex
  have hmin : ∀ m, n₀ ≤ f m := by
    intro m
    by_contra hlt
    push Not at hlt
    exact Nat.find_min hex hlt ⟨m, rfl⟩
  have hcardconst : ∀ k, m₀ ≤ k → f k = n₀ := by
    intro k hk
    have h1 : n₀ ≤ f k := hmin k
    have h2 : f k ≤ f m₀ :=
      Nat.le_induction (m := m₀) (P := fun l _ => f l ≤ f m₀) le_rfl
        (fun l _ ih => (hfanti l).trans ih) k hk
    omega
  have hconst : ∀ k : ℕ, m₀ ≤ k →
      X.arcStab (-(k : ℤ)) (k : ℤ) = X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) := by
    intro k hk
    have hfk : Nat.card ↥(X.arcStab (-(k : ℤ)) (k : ℤ)) = n₀ := by
      have := hcardconst k hk
      simpa using this
    have hfm : Nat.card ↥(X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) = n₀ := by
      have := hm₀
      simpa using this
    have hcard : Nat.card ↥(X.arcStab (-(k : ℤ)) (k : ℤ)) =
        Nat.card ↥(X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) := by rw [hfk, hfm]
    haveI : Finite ↥(X.arcStab (-(k : ℤ)) (k : ℤ)) :=
      finite_of_le_stabilizer X.hyp (H := X.arcStab (-(k : ℤ)) (k : ℤ))
        (X.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    haveI : Finite ↥(X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ)) :=
      finite_of_le_stabilizer X.hyp (H := X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ))
        (X.arcStab_le_Gi_of_between (k := 0) (by omega) (by omega))
    have hle : X.arcStab (-(k : ℤ)) (k : ℤ) ≤ X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) :=
      X.arcStab_anti (by omega) (by omega)
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hAeq : X.arcStab (-(m₀ : ℤ)) (m₀ : ℤ) = X.GT := by
    refine le_antisymm ?_ (X.GT_le_arcStab _ _)
    intro g hg
    rw [Setup.GT, Fan86.mem_fixSet]
    rintro v ⟨i, rfl⟩
    have hk : ∀ k : ℕ, m₀ ≤ k → g ∈ X.arcStab (-(k : ℤ)) (k : ℤ) := by
      intro k hk; rw [hconst k hk]; exact hg
    let k : ℕ := max m₀ i.natAbs
    have hmem := hk k (le_max_left _ _)
    have hi1 : i ≤ (k : ℤ) := by
      have h2 : (i.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast le_max_right m₀ i.natAbs
      have h3 : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
      omega
    have hi2 : -(k : ℤ) ≤ i := by
      have h2 : (i.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast le_max_right m₀ i.natAbs
      have h4 : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h4
      omega
    exact (Fan86.mem_fixSet.mp hmem) (X.vert i) ⟨i, by rw [Set.mem_Icc]; exact ⟨hi2, hi1⟩, rfl⟩
  have hbig : ∀ (a : ℤ) (ℓ : ℕ), 2 * m₀ + 1 ≤ ℓ → X.arcStab a (a + ℓ) = X.GT := by
    intro a ℓ hℓ
    refine le_antisymm ?_ (X.GT_le_arcStab a (a + ℓ))
    have hconj : ∀ k : ℤ, X.arcStab (-(m₀ : ℤ) + 2 * k) ((m₀ : ℤ) + 2 * k) = X.GT := by
      intro k
      rw [X.arcStab_add k (-(m₀ : ℤ)) (m₀ : ℤ), hAeq]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem X.tau_mem_normalizer_GT k)
    have hcast : (m₀ : ℤ) + 1 ≤ (ℓ : ℤ) := by
      have h1 : m₀ + 1 ≤ ℓ := by omega
      exact_mod_cast h1
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (a + (m₀ : ℤ))
    · have hj1 : a ≤ -(m₀ : ℤ) + 2 * j := by linarith
      have hj2 : (m₀ : ℤ) + 2 * j ≤ a + ℓ := by linarith
      rw [← hconj j]
      exact X.arcStab_anti hj1 hj2
    · have hj1 : a ≤ -(m₀ : ℤ) + 2 * (j + 1) := by linarith
      have hj2 : (m₀ : ℤ) + 2 * (j + 1) ≤ a + ℓ := by linarith
      rw [← hconj (j + 1)]
      exact X.arcStab_anti hj1 hj2
  have hGT_ne_G0 : X.Gi 0 ≠ X.GT := by
    intro hEq
    have hadj01 : Γ.Adj (X.vert 0) (X.vert 1) := by simpa using X.adj 0
    have hle : X.Gi 0 ≤ X.Gi 1 := hEq.symm ▸ X.GT_le_Gi 1
    obtain ⟨b, hb, hb1⟩ := X.hyp.exists_adj_ne (X.vert 0) (X.vert 1)
    obtain ⟨g, hg, hgb⟩ := X.hyp.locTrans hb hadj01
    have hg1 : g • X.vert 1 = X.vert 1 :=
      MulAction.mem_stabilizer_iff.mp (hle hg)
    rw [← hg1] at hgb
    exact hb1 (MulAction.injective g hgb)
  let P : ℕ → Prop := fun ℓ => ∃ a : ℤ, X.arcStab a (a + ℓ) ≠ X.GT
  have hP0 : P 0 := by
    refine ⟨0, ?_⟩
    rw [show (0 : ℤ) + ((0 : ℕ) : ℤ) = 0 by norm_num, X.arcStab_self]
    exact hGT_ne_G0
  have hbdd : ∀ ℓ : ℕ, P ℓ → ℓ ≤ 2 * m₀ := by
    rintro ℓ ⟨a, ha⟩
    by_contra h
    exact ha (hbig a ℓ (by omega))
  let ℓ : ℕ := Nat.findGreatest P (2 * m₀)
  have hPℓ : P ℓ := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hℓb : ℓ ≤ 2 * m₀ := Nat.findGreatest_le _
  have hmaxP : ∀ n, ℓ < n → n ≤ 2 * m₀ → ¬ P n := (Nat.findGreatest_eq_iff.1 rfl).2.2
  have hPℓ1 : ¬ P (ℓ + 1) := by
    by_cases h : ℓ + 1 ≤ 2 * m₀
    · exact hmaxP (ℓ + 1) (by omega) h
    · rintro ⟨a, ha⟩
      exact absurd (hbdd (ℓ + 1) ⟨a, ha⟩) (by omega)
  obtain ⟨a, ha⟩ := hPℓ
  have hPinit : P (s - 1) := by
    refine ⟨0, ?_⟩
    rw [show (0 : ℤ) + (((s - 1 : ℕ) : ℤ)) = ((s - 1 : ℕ) : ℤ) from zero_add _]
    intro hEq
    have hR : X.RightTransAt 0 (((s - 1 : ℕ)) : ℤ) := by
      have h := (hs.2.1 (s - 1) (by omega) (by omega) (X.line.arc 0 (s - 1))).2
      have h' := (X.rightTransitive_arc_iff 0 (by omega)).mp h
      simpa using h'
    exact X.arcStab_ne_GT_of_rightTransAt (m := 0) (r := (((s - 1 : ℕ)) : ℤ)) (by omega) hR hEq
  have hℓs : s - 1 ≤ ℓ := Nat.le_findGreatest (hbdd (s - 1) hPinit) hPinit
  have hℓ2 : 2 ≤ ℓ := by omega
  have hright : X.RightTransAt a (a + ℓ) := by
    by_contra hsing
    have hPleQ : pCoreOf 2 (X.arcStab a (a + ℓ)) ≤ X.Q (a + ℓ) :=
      X.pCoreOf_arcStab_le_Q_right a (a + ℓ) (by omega) hsing
    have hKA : X.K ≤ X.arcStab a (a + ℓ) := X.K_le_GT.trans (X.GT_le_arcStab _ _)
    have hAle : X.arcStab a (a + ℓ) ≤ X.Gi (a + ℓ - 1) ⊓ X.Gi (a + ℓ - 1 + 1) := by
      rw [show a + (ℓ : ℤ) - 1 + 1 = a + ℓ by ring]
      exact le_inf (X.arcStab_le_Gi_of_between (by omega) (by omega))
        (X.arcStab_le_Gi_of_between (by omega) (by omega))
    obtain ⟨-, hAdecomp⟩ := X.pCoreOf_eq_inf_edgeSylow (a + ℓ - 1) hKA hAle
    have hA_le_Gb1 : X.arcStab a (a + ℓ) ≤ X.Gi (a + ℓ + 1) := by
      rw [← hAdecomp]
      exact sup_le (X.K_le_Gi (a + ℓ + 1))
        (hPleQ.trans ((X.Q_le_Gi_adj (a + ℓ)).trans inf_le_right))
    have hGT : X.arcStab a (a + ((ℓ + 1 : ℕ) : ℤ)) = X.GT := by
      by_contra h
      exact hPℓ1 ⟨a, h⟩
    have hAleGT : X.arcStab a (a + ℓ) ≤ X.GT := by
      rw [← hGT, X.arcStab_eq_inf (show a ≤ a + ((ℓ + 1 : ℕ) : ℤ) by omega)]
      refine le_inf (X.arcStab_le_Gi_left (by omega)) ?_
      rw [show a + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ + 1 by push_cast; ring]
      exact hA_le_Gb1
    exact ha (le_antisymm hAleGT (X.GT_le_arcStab _ _))
  have hleft : X.LeftTransAt a (a + ℓ) := by
    by_contra hsing
    have hPleQ : pCoreOf 2 (X.arcStab a (a + ℓ)) ≤ X.Q a :=
      X.pCoreOf_arcStab_le_Q_left a (a + ℓ) (by omega) hsing
    have hKA : X.K ≤ X.arcStab a (a + ℓ) := X.K_le_GT.trans (X.GT_le_arcStab _ _)
    have hAle : X.arcStab a (a + ℓ) ≤ X.Gi a ⊓ X.Gi (a + 1) :=
      le_inf (X.arcStab_le_Gi_left (by omega)) (X.arcStab_le_Gi_of_between (by omega) (by omega))
    obtain ⟨-, hAdecomp⟩ := X.pCoreOf_eq_inf_edgeSylow a hKA (by
      rw [show a + 1 = a + 1 by rfl]; exact hAle)
    have hA_le_Gam1 : X.arcStab a (a + ℓ) ≤ X.Gi (a - 1) := by
      rw [← hAdecomp]
      exact sup_le (X.K_le_Gi (a - 1))
        (hPleQ.trans ((X.Q_le_Gi_adj a).trans inf_le_left))
    have hGT : X.arcStab (a - 1) ((a - 1) + ((ℓ + 1 : ℕ) : ℤ)) = X.GT := by
      by_contra h
      refine hPℓ1 ⟨a - 1, ?_⟩
      simpa only [show a - 1 + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ by push_cast; ring] using h
    have hAleGT : X.arcStab a (a + ℓ) ≤ X.GT := by
      rw [← hGT, X.arcStab_eq_inf (show a - 1 ≤ (a - 1) + ((ℓ + 1 : ℕ) : ℤ) by omega)]
      exact le_inf hA_le_Gam1 (by
        rw [show (a - 1) + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ by push_cast; ring]
        exact X.arcStab_le_Gi_right (by omega))
    exact ha (le_antisymm hAleGT (X.GT_le_arcStab _ _))
  obtain ⟨a', j, m, ha'j, hℓm, hleft', hright', hextR, hextL⟩ :
      ∃ (a' : ℤ) (j : ℤ) (m : ℕ), a' = 2 * j ∧ ℓ = 2 * m ∧
        X.LeftTransAt a' (a' + ℓ) ∧ X.RightTransAt a' (a' + ℓ) ∧
        X.arcStab a' (a' + ℓ + 1) = X.GT ∧ X.arcStab (a' - 1) (a' + ℓ) = X.GT := by
    have hextR0 : X.arcStab a (a + ((ℓ + 1 : ℕ) : ℤ)) = X.GT := by
      by_contra h
      exact hPℓ1 ⟨a, h⟩
    have hextR1 : X.arcStab a (a + ℓ + 1) = X.GT := by
      rwa [show a + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ + 1 by push_cast; ring] at hextR0
    have hextL0 : X.arcStab (a - 1) ((a - 1) + ((ℓ + 1 : ℕ) : ℤ)) = X.GT := by
      by_contra h
      refine hPℓ1 ⟨a - 1, ?_⟩
      simpa only [show a - 1 + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ by push_cast; ring] using h
    have hextL1 : X.arcStab (a - 1) (a + ℓ) = X.GT := by
      rwa [show (a - 1) + ((ℓ + 1 : ℕ) : ℤ) = a + ℓ by push_cast; ring] at hextL0
    by_cases hℓge : s ≤ ℓ
    ·
      have hreg : Regular Γ G (X.line.arc a ℓ) :=
        ⟨(X.leftTransitive_arc_iff a ℓ).mpr hleft,
          (X.rightTransitive_arc_iff a (by omega)).mpr hright⟩
      obtain ⟨h0, h1⟩ := (odd_orbit_of_rightSingular X.hyp.isTree X.hyp.adj_smul
        (fun v x y hx hy => X.hyp.locTrans hx hy) X.hyp.edgeTrans X.hyp.preservesParts hs hX).2
        ℓ hℓge (X.line.arc a ℓ) hreg
      have h0' : Even (Γ.dist (X.vert 0) (X.vert a)) := by simpa [Line.arc] using h0
      have h1' : Even (Γ.dist (X.vert 0) (X.vert (a + ℓ))) := by simpa [Line.arc] using h1
      have ha_even : Even a := X.even_of_even_dist a h0'
      have hab_even : Even (a + ℓ) := X.even_of_even_dist (a + ℓ) h1'
      obtain ⟨j, hj⟩ := ha_even
      obtain ⟨k, hk⟩ := hab_even
      have hℓZ : (ℓ : ℤ) = (k - j) + (k - j) := by omega
      have hkj : (0 : ℤ) ≤ k - j := by omega
      have hℓm : ℓ = 2 * (k - j).toNat := by
        have hcast : ((k - j).toNat : ℤ) = k - j := Int.toNat_of_nonneg hkj
        have : (ℓ : ℤ) = ((k - j).toNat : ℤ) + ((k - j).toNat : ℤ) := by omega
        omega
      exact ⟨a, j, (k - j).toNat, by omega, hℓm, hleft, hright, hextR1, hextL1⟩
    ·
      have hℓlt : ℓ < s := by omega
      have hℓeq : ℓ = s - 1 := by omega
      obtain ⟨k, hk⟩ := hodd
      have hℓeven : Even ℓ := by
        refine ⟨k, ?_⟩
        omega
      obtain ⟨m, hm⟩ := hℓeven
      have hm2 : ℓ = 2 * m := by omega
      have hL : ∀ b : ℤ, X.LeftTransAt b (b + ℓ) := fun b =>
        (X.trans_of_lt hs b (by omega) (by omega)).1
      have hR : ∀ b : ℤ, X.RightTransAt b (b + ℓ) := fun b =>
        (X.trans_of_lt hs b (by omega) (by omega)).2
      have heR : ∀ b : ℤ, X.arcStab b (b + ℓ + 1) = X.GT := by
        intro b
        by_contra h
        refine hPℓ1 ⟨b, ?_⟩
        simpa only [show b + ((ℓ + 1 : ℕ) : ℤ) = b + ℓ + 1 by push_cast; ring] using h
      have heL : ∀ b : ℤ, X.arcStab (b - 1) (b + ℓ) = X.GT := by
        intro b
        have h := heR (b - 1)
        rwa [show b - 1 + ℓ + 1 = b + ℓ by ring] at h
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' a
      · exact ⟨a, j, m, by omega, hm2, hL a, hR a, heR a, heL a⟩
      · exact ⟨a + 1, j + 1, m, by omega, hm2, hL (a + 1), hR (a + 1),
          heR (a + 1), heL (a + 1)⟩
  have hpt : a' + 2 * (-j) = (0 : ℤ) := by omega
  have hend : a' + (ℓ : ℤ) + 2 * (-j) = 2 * (m : ℤ) := by omega
  have hleft0 : X.LeftTransAt 0 (2 * (m : ℤ)) := by
    have h := X.leftTransAt_add (-j) a' (a' + ℓ) hleft'
    rwa [hpt, hend] at h
  have hright0 : X.RightTransAt 0 (2 * (m : ℤ)) := by
    have h := X.rightTransAt_add (-j) a' (a' + ℓ) hright'
    rwa [hpt, hend] at h
  have hGTconj : conjSub (X.τ ^ (-j)) X.GT = X.GT :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (zpow_mem X.tau_mem_normalizer_GT (-j))
  have hextR0 : X.arcStab 0 (2 * (m : ℤ) + 1) = X.GT := by
    have h := X.arcStab_add (-j) a' (a' + ℓ + 1)
    rw [hpt, show a' + ℓ + 1 + 2 * (-j) = 2 * (m : ℤ) + 1 by omega] at h
    rw [h, hextR, hGTconj]
  have hextL0 : X.arcStab (0 - 1) (2 * (m : ℤ)) = X.GT := by
    have h := X.arcStab_add (-j) (a' - 1) (a' + ℓ)
    rw [show a' - 1 + 2 * (-j) = (0 : ℤ) - 1 by omega,
      show a' + ℓ + 2 * (-j) = 2 * (m : ℤ) by omega] at h
    rw [h, hextL, hGTconj]
  exact ⟨m, by omega, by omega, hleft0, hright0, hextR0, hextL0⟩

end Setup

end CFSG.Quasithin.St84
