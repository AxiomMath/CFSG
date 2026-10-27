module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin
open CFSG.LieType.Ree CFSG.StandardType.LieKnownR2.Short

private theorem rckShort_mat_elt {n : ℕ} {F : Type} [Field F] (r : RootSubgroupIndex n) (c : F) :
    mat n F (elt r c) = 1 + c • E F r :=
  mat_elt r c

private theorem rckShort_commute_elt {n : ℕ} {F : Type} [Field F] (r : RootSubgroupIndex n)
    {c₀ : F} (hc₀ : c₀ ≠ 0) {k : StatedSp n F} (h : Commute k (elt r c₀)) (c : F) :
    Commute k (elt r c) := by
  have hm0 : Commute (mat n F k) (mat n F (elt r c₀)) := h.map (mat n F)
  have hm : Commute (mat n F k) (1 + c₀ • E F r) := by
    rwa [rckShort_mat_elt] at hm0
  have hmat : Commute (mat n F k) (1 + c • E F r) :=
    commute_one_add_smul_of_ne_zero hc₀ hm c
  have hmat' : Commute (mat n F k) (mat n F (elt r c)) := by
    rwa [← rckShort_mat_elt] at hmat
  exact Commute.of_map mat_injective hmat'

private theorem rckShort_rootGroup_cent {n : ℕ} {F : Type} [Field F] {β : Fin n → ℤ}
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) :
    ∀ x ∈ rootGroup n F β, x ≠ 1 →
      Subgroup.centralizer {x} ≤
        Subgroup.centralizer (rootGroup n F β : Set (StatedSp n F)) := by
  intro x hx hx1 k hk
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨c₀, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  have hc₀ : c₀ ≠ 0 := by
    intro hc
    exact hx1 (by rw [hc, elt_zero])
  have hcomm : Commute k (elt r c₀) := Subgroup.mem_centralizer_singleton_iff.mp hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hy
  exact (rckShort_commute_elt r hc₀ hcomm c).symm

private theorem rckShort_pCoreOf_le {X : Type*} [Group X] (H : Subgroup X) :
    pCoreOf 2 H ≤ H := by
  intro k hk
  rw [pCoreOf] at hk
  obtain ⟨a, _ha, hak⟩ := Subgroup.mem_map.mp hk
  rw [← hak]
  exact a.property

private theorem rckShort_exists_pow_two_eq_one_of_mem_pCoreOf {X : Type*} [Group X]
    {H : Subgroup X} {k : X} (hk : k ∈ pCoreOf 2 H) :
    ∃ b : ℕ, k ^ (2 ^ b) = 1 := by
  have hP : IsPGroup 2 (pCoreOf 2 H) := by
    change IsPGroup 2 ((pCore 2 ↥H).map H.subtype)
    exact (pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  obtain ⟨b, hb⟩ := hP ⟨k, hk⟩
  exact ⟨b, by simpa using congrArg (Subtype.val) hb⟩

private theorem rckShort_conj_pow_apply {G : Type*} [Group G] {k y z : G}
    (hz : z ∈ Subgroup.center G) (h : k * y * k⁻¹ = z * y) (n : ℕ) :
    ((MulAut.conj k) ^ n) y = z ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul]
    have hzpow : (MulAut.conj k) (z ^ n) = z ^ n := by
      rw [MulAut.conj_apply]
      have hzc : z ^ n ∈ Subgroup.center G := pow_mem hz n
      have hcomm := Subgroup.mem_center_iff.mp hzc k
      rw [hcomm]; group
    rw [hzpow, MulAut.conj_apply, h, pow_succ]
    group

@[expose] def RCKK2NbrRootSubShortAt
    (t' : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R : Subgroup X) (m g : ℕ)
    (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' → 1 ≤ g → β ∈ (ggU t' m g).D.roots →
    ¬ GGLongRoot (ggU t' m g).D β → GGShortTag t' → 2 • β ∉ (ggU t' m g).D.roots →
    GGRootVia (ggU t' m g) K R β → ∀ r ∈ R, r ≠ 1 →
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X)

theorem rckK2NbrRootSubShort_of_at
    (h : ∀ t', GGPosTag t' → GGShortTag t' → RCKK2NbrRootSubShortAt t') : RCKK2NbrRootSubShort := by
  intro X _ _ K R t' m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact h t' ht hS X K R m g β ht hg hβ hL hS h2 hvia r hr hr1

theorem rckGL1_of_cent
    {X : Type} [Group X] [Finite X] {K R : Subgroup X}
    {t' : StatedLieTag} {m g : ℕ} {β : Fin (ggU t' m g).D.rank → ℤ} (ht : GGPosTag t')
    (hg : 1 ≤ g) (hPM : t' = .POmegaMinus → 2 ≤ m) (hcent : RCKLemmaHCent (ggU t' m g) β)
    (hvia : GGRootVia (ggU t' m g) K R β) {r : X} (hr : r ∈ R) (hr1 : r ≠ 1) :
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X) := by
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  intro k hk
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  have hkH : k ∈ K ⊓ Subgroup.centralizer ({r} : Set X) :=
    rckShort_pCoreOf_le (K ⊓ Subgroup.centralizer ({r} : Set X)) hk
  have hkr : k * r = r * k := Subgroup.mem_centralizer_singleton_iff.mp hkH.2
  have hkK : k ∈ K := hkH.1
  have hkrange : k ∈ φ.range := hφrange ▸ hkK
  obtain ⟨k', hk'eq⟩ := hkrange
  rw [hR] at hs hr
  obtain ⟨y', hy'mem, hy's⟩ := Subgroup.mem_map.mp hs
  obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hy'mem
  obtain ⟨y, hymem, hyr⟩ := Subgroup.mem_map.mp hr
  obtain ⟨x, hxmem, hxeq⟩ := Subgroup.mem_map.mp hymem
  have hxeq' : u * x * u⁻¹ = y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxeq
  have hx'eq' : u * x' * u⁻¹ = y' := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hx'eq
  have hx1 : x ≠ 1 := by
    intro hx0
    apply hr1
    rw [← hyr, ← hxeq', hx0]
    simp
  set z : (ggU t' m g).K := k' * y * k'⁻¹ * y⁻¹ with hzdef
  have hzker : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hzdef, hk'eq, hyr]
    have h1 : k * r * k⁻¹ = r := by rw [hkr]; group
    rw [h1, mul_inv_cancel]
  have hzcenter : z ∈ Subgroup.center (ggU t' m g).K := hφker hzker
  have hzy : k' * y * k'⁻¹ = z * y := by rw [hzdef]; group
  obtain ⟨b, hkb⟩ := rckShort_exists_pow_two_eq_one_of_mem_pCoreOf hk
  have hk'pow_ker : k' ^ (2 ^ b) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk'eq, hkb]
  have hk'pow_center : k' ^ (2 ^ b) ∈ Subgroup.center (ggU t' m g).K := hφker hk'pow_ker
  have hconj := rckShort_conj_pow_apply hzcenter hzy (2 ^ b)
  have hconj_triv : ((MulAut.conj k') ^ (2 ^ b)) y = y := by
    rw [← map_pow, MulAut.conj_apply]
    have hcomm := Subgroup.mem_center_iff.mp hk'pow_center y
    rw [← hcomm]; group
  rw [hconj_triv] at hconj
  have hzpow : z ^ (2 ^ b) = 1 := by
    have h : (1 : (ggU t' m g).K) * y = z ^ (2 ^ b) * y := by simpa using hconj
    exact (mul_right_cancel h).symm
  have hz1 : z = 1 := rckGL1_eq_one_of_pow_two_eq_one_of_centerPPrime
    (rckGL1_centerPPrime_ggU ht hg hPM) hzcenter b hzpow
  have hk'y : k' * y = y * k' := by
    have h1 : k' * y * k'⁻¹ = y := by rw [hzy, hz1, one_mul]
    calc k' * y = k' * y * k'⁻¹ * k' := by group
      _ = y * k' := by rw [h1]
  have hcomm_x : (u⁻¹ * k' * u) * x = x * (u⁻¹ * k' * u) := by
    have h := hk'y
    rw [← hxeq'] at h
    calc (u⁻¹ * k' * u) * x = u⁻¹ * (k' * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * k') * u := by rw [h]
      _ = x * (u⁻¹ * k' * u) := by group
  have hux_mem : u⁻¹ * k' * u ∈ Subgroup.centralizer ({x} : Set (ggU t' m g).K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_x
  have hux_root : u⁻¹ * k' * u ∈
      Subgroup.centralizer ((ggU t' m g).D.rootGroup β : Set (ggU t' m g).K) :=
    hcent x hxmem hx1 hux_mem
  have hx'comm : x' * (u⁻¹ * k' * u) = (u⁻¹ * k' * u) * x' :=
    Subgroup.mem_centralizer_iff.mp hux_root x' hx'mem
  have hk'y' : k' * y' = y' * k' := by
    have h := hx'comm.symm
    calc k' * y' = u * (u⁻¹ * k' * u * x') * u⁻¹ := by rw [← hx'eq']; group
      _ = u * (x' * (u⁻¹ * k' * u)) * u⁻¹ := by rw [h]
      _ = y' * k' := by rw [← hx'eq']; group
  rw [← hk'eq, ← hy's, ← map_mul, ← map_mul, hk'y']

theorem rck_lemmaHC_BC_short
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSp m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSp m g).D.roots) : RCKLemmaHCent (ggU .PSp m g) β := by
  change RCKLemmaHCent
    ⟨StatedSp m (GaloisField 2 g), Symplectic.rootDatum m (GaloisField 2 g)⟩ β
  exact rckShort_rootGroup_cent hβ

theorem rck_lemmaHC_F4_short
    {n f : ℕ} (hf : 1 ≤ f) {β : Fin (ggU .F4 n f).D.rank → ℤ}
    (hβ : β ∈ (ggU .F4 n f).D.roots) (hs : ¬ GGLongRoot (ggU .F4 n f).D β) :
    RCKLemmaHCent (ggU .F4 n f) β := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 f) ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 f) 2)
  let φ : MulAut (ggU .F4 n f).K := ReeTag.F4.finiteExceptionalAut (GaloisField 2 f)
  obtain ⟨β', hβ', hXβ', hXmβ', hlong⟩ :=
    finiteExceptionalAut_F4_map_rootGroup (K := GaloisField 2 f) (β := β) hβ
  have hXβ'' : ((ggU .F4 n f).D.rootGroup β).map φ.toMonoidHom =
      (ggU .F4 n f).D.rootGroup β' := hXβ'
  have hl' : GGLongRoot (ggU .F4 n f).D β' := hlong.mpr hs
  have hcent' : RCKLemmaHCent (ggU .F4 n f) β' :=
    rck_lemmaH_of_parts (rck_lemmaH_F4 hf hl').1 (rck_lemmaH_F4 hf hl').2
  intro x hx hx1 k hk
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hxmem' : φ x ∈ (ggU .F4 n f).D.rootGroup β' := by
    rw [← hXβ'']; exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
  have hx1' : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.mp hk
  have hkx' : φ k * φ x = φ x * φ k := by
    rw [← map_mul, ← map_mul, hkx]
  have hφkmem : φ k ∈ Subgroup.centralizer ({φ x} : Set (ggU .F4 n f).K) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hkx'
  have hφkroot : φ k ∈ Subgroup.centralizer ((ggU .F4 n f).D.rootGroup β' :
      Set (ggU .F4 n f).K) :=
    hcent' (φ x) hxmem' hx1' hφkmem
  have hy' : φ y ∈ (ggU .F4 n f).D.rootGroup β' := by
    rw [← hXβ'']; exact Subgroup.mem_map_of_mem φ.toMonoidHom hy
  have hcomm : φ y * φ k = φ k * φ y :=
    Subgroup.mem_centralizer_iff.mp hφkroot (φ y) hy'
  exact φ.injective (by rw [map_mul, map_mul, hcomm])

theorem rckK2NbrRootSubShortAt_PSp
    : RCKK2NbrRootSubShortAt .PSp := by
  intro X _ _ K R m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact rckGL1_of_cent ht hg (fun h => absurd h (by decide))
    (rck_lemmaHC_BC_short hg hβ) hvia hr hr1

theorem rckK2NbrRootSubShortAt_F4
    : RCKK2NbrRootSubShortAt .F4 := by
  intro X _ _ K R m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact rckGL1_of_cent ht hg (fun h => absurd h (by decide))
    (rck_lemmaHC_F4_short hg hβ hL) hvia hr hr1

end CFSG.StandardType.RCKC1
