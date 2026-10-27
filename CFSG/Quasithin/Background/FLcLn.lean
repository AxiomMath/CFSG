module

public import CFSG.Quasithin.Background.FLcAbs
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLcAut

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits

variable {A : Type} [Group A]

theorem le_normalizer_of_conj_mem {X L : Subgroup A}
    (h : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) : X ≤ Subgroup.normalizer (L : Set A) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨h x hx l, fun hl => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hl
  have e : x⁻¹ * (x * l * x⁻¹) * x⁻¹⁻¹ = l := by group
  rwa [e] at this

theorem conjSub_eq_of_conj_mem {S P : Subgroup A}
    (h : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) {s : A} (hs : s ∈ S) : conjSub s P = P := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have := h s hs _ hx
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    have := h s⁻¹ (S.inv_mem hs) _ hx
    simpa using this

theorem le_normalizer_of_conj_mem' {S P : Subgroup A}
    (h : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) : S ≤ Subgroup.normalizer (P : Set A) :=
  le_normalizer_of_conj_mem h

theorem mem_sup_prod_of_conj {L S : Subgroup A} (hn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    ∀ x ∈ L ⊔ S, ∃ l ∈ L, ∃ s ∈ S, x = l * s := by
  let LS : Subgroup A :=
    { carrier := {x | ∃ l ∈ L, ∃ s ∈ S, x = l * s}
      one_mem' := ⟨1, L.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l, hl, s, hs, rfl⟩ ⟨l', hl', s', hs', rfl⟩
        refine ⟨l * (s * l' * s⁻¹), L.mul_mem hl (hn s hs l' hl'), s * s', S.mul_mem hs hs', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, s, hs, rfl⟩
        refine ⟨s⁻¹ * l⁻¹ * s⁻¹⁻¹, ?_, s⁻¹, S.inv_mem hs, ?_⟩
        · exact hn s⁻¹ (S.inv_mem hs) l⁻¹ (L.inv_mem hl)
        · group }
  have hle : L ⊔ S ≤ LS :=
    sup_le (fun l hl => ⟨l, hl, 1, S.one_mem, by simp⟩) (fun s hs => ⟨1, L.one_mem, s, hs, by simp⟩)
  intro x hx
  exact hle hx

theorem center_trivial_of_equiv {H : Type*} [Group H] {n : ℕ} (e : H ≃* SLt n) {z : H}
    (hz : ∀ h : H, h * z = z * h) : z = 1 := by
  have h1 : e z ∈ Subgroup.center (SLt n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz h]
  rw [← scalars_eq_center,
    CFSG.LieType.SteinbergBR.BinaryLinear.scalars_eq_bot (Nat.card_zmod 2)] at h1
  have h2 : e z = 1 := h1
  exact e.injective (by rw [h2, map_one])

theorem eq_one_of_centralizes [Finite A] {L X S : Subgroup A} {n : ℕ} (e : ↥L ≃* SLt n)
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S)
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) {c : A} (hcX : c ∈ X)
    (hc : ∀ l ∈ L, c * l * c⁻¹ = l) : c = 1 := by
  let C : Subgroup A := Subgroup.centralizer (L : Set A) ⊓ X
  have hCmem : ∀ y : A, y ∈ C ↔ y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ = l := by
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨hy2, fun l hl => ?_⟩
      have := Subgroup.mem_centralizer_iff.1 hy1 l hl
      rw [← this]
      group
    · rintro ⟨hy2, hy1⟩
      refine ⟨Subgroup.mem_centralizer_iff.2 fun l hl => ?_, hy2⟩
      have := hy1 l hl
      calc l * y = (y * l * y⁻¹) * y := by rw [this]
        _ = y * l := by group
  have hSn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl => hLn s (hS.1 hs) l hl
  have hCX : C ≤ X := inf_le_right
  have hCnormal : (C.subgroupOf X).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨hyX, hyc⟩ := (hCmem _).1 hy
    rw [hCmem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨X.mul_mem (X.mul_mem x.2 hyX) (X.inv_mem x.2), fun l hl => ?_⟩
    have hxl : (x : A)⁻¹ * l * (x : A) ∈ L := by
      have := hLn (x : A)⁻¹ (X.inv_mem x.2) l hl
      simpa using this
    have h1 := hyc _ hxl
    calc (x : A) * (y : A) * (x : A)⁻¹ * l * ((x : A) * (y : A) * (x : A)⁻¹)⁻¹
        = (x : A) * ((y : A) * ((x : A)⁻¹ * l * (x : A)) * (y : A)⁻¹) * (x : A)⁻¹ := by group
      _ = (x : A) * ((x : A)⁻¹ * l * (x : A)) * (x : A)⁻¹ := by rw [h1]
      _ = l := by group
  have hCp : IsPGroup 2 ↥C := by
    rintro ⟨y, hy⟩
    obtain ⟨hyX, hyc⟩ := (hCmem y).1 hy
    obtain ⟨l, hl, s, hs, rfl⟩ := mem_sup_prod_of_conj hSn y (hXLS hyX)
    obtain ⟨a, ha⟩ := hS.2.1 ⟨s, hs⟩
    have hsa : s ^ (2 ^ a) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hpow : ∀ m : ℕ, ∃ l' ∈ L, (l * s) ^ m = l' * s ^ m := by
      intro m
      induction m with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨l', hl', hm⟩ := ih
        have hsm : s ^ m ∈ S := S.pow_mem hs m
        refine ⟨l' * (s ^ m * l * (s ^ m)⁻¹), L.mul_mem hl' (hSn _ hsm l hl), ?_⟩
        have key : ∀ t : A, l' * t * (l * s) = (l' * (t * l * t⁻¹)) * (t * s) := fun t => by group
        rw [pow_succ, hm, pow_succ, key]
    obtain ⟨l', hl', hm⟩ := hpow (2 ^ a)
    rw [hsa, mul_one] at hm
    have hzC : (l * s) ^ (2 ^ a) ∈ C := C.pow_mem hy _
    rw [hm] at hzC
    have hcomm := ((hCmem l').1 hzC).2
    have hz1 : (⟨l', hl'⟩ : ↥L) = 1 := by
      refine center_trivial_of_equiv e (fun h => ?_)
      apply Subtype.ext
      have h1 := hcomm h h.2
      show (h : A) * l' = l' * (h : A)
      calc (h : A) * l' = (l' * (h : A) * l'⁻¹) * l' := by rw [h1]
        _ = l' * (h : A) := by group
    refine ⟨a, ?_⟩
    apply Subtype.ext
    show (l * s) ^ (2 ^ a) = 1
    rw [hm]
    exact congrArg Subtype.val hz1
  have hle : C ≤ CFSG.Open.pCoreOf 2 X := le_pCoreOf 2 hCX hCnormal hCp
  rw [hO2] at hle
  have := hle ((hCmem c).2 ⟨hcX, hc⟩)
  simpa using this

theorem exists_borelIso [Finite A] {L B : Subgroup A} {n : ℕ} (hn : 1 ≤ n) (hB : IsSylowTwoOf B L)
    (e₀ : ↥L ≃* SLt n) : Nonempty (BorelIso n L B) := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 (SLt n) := Sylow.mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  have hQ : (Q : Subgroup (SLt n)) = (P : Subgroup ↥L).map e₀.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular hn Q
  refine ⟨⟨e₀.trans (MulAut.conj g⁻¹), ?_⟩⟩
  have h1 : (B.subgroupOf L).map e₀.toMonoidHom = conjSub g (Ut n) := by
    rw [← hP, ← hQ, hg]
    rfl
  have h2 : (B.subgroupOf L).map (e₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
      conjSub g⁻¹ ((B.subgroupOf L).map e₀.toMonoidHom) := by
    rw [conjSub, Subgroup.map_map]
    rfl
  rw [h2, h1, conjSub_inv_conjSub]

theorem autOf_swap [Finite A] {L X S : Subgroup A} {n : ℕ} (hn : 3 ≤ n)
    (D : BorelIso n L (S ⊓ L)) (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) {s : A}
    (hsS : s ∈ S) (hsL : s ∉ L) (hsN : s ∈ Subgroup.normalizer (L : Set A)) :
    ∀ d, 1 ≤ d → d < n → (stabilizer (flagSpace n (ZMod 2) d)).map
      (D.autOf s hsN).toMonoidHom = stabilizer (flagSpace n (ZMod 2) (n - d)) := by
  have hBs : conjSub s (S ⊓ L) = S ⊓ L := by
    ext x
    rw [mem_conjSub]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := S.mul_mem (S.mul_mem hsS h1) (S.inv_mem hsS)
        simpa [mul_assoc] using this
      · have := (Subgroup.mem_normalizer_iff.1 hsN _).1 h2
        simpa [mul_assoc] using this
    · rintro ⟨h1, h2⟩
      refine ⟨S.mul_mem (S.mul_mem (S.inv_mem hsS) h1) hsS, ?_⟩
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hsN) x).1 h2
      simpa using this
  have hφ : (Ut n).map (D.autOf s hsN).toMonoidHom = Ut n := by
    have := D.model_conjSub s hsN (S ⊓ L)
    rw [hBs, D.model_B] at this
    exact this
  rcases aut_dichotomy hn (D.autOf s hsN) hφ with ⟨b, hbU, hb⟩ | h
  · exfalso
    have hbB : b ∈ D.model (S ⊓ L) := by rw [D.model_B]; exact hbU
    obtain ⟨y, hy, rfl⟩ := hbB
    have hyB : (y : A) ∈ S ⊓ L := hy
    have hconj : ∀ l : ↥L, s * (l : A) * s⁻¹ = (y : A) * (l : A) * (y : A)⁻¹ := by
      intro l
      have h1 := hb (D.e l)
      rw [D.autOf_e] at h1
      have h2 : L.normalizerMonoidHom ⟨s, hsN⟩ l = y * l * y⁻¹ := by
        apply D.e.injective
        rw [h1]
        simp
      have h3 := congrArg Subtype.val h2
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
      simpa using h3
    have hcX : (y : A)⁻¹ * s ∈ X :=
      X.mul_mem (X.inv_mem (hLX y.2)) (hS.1 hsS)
    have hc : ∀ l ∈ L, (y : A)⁻¹ * s * l * ((y : A)⁻¹ * s)⁻¹ = l := by
      intro l hl
      have h1 := hconj ⟨l, hl⟩
      calc (y : A)⁻¹ * s * l * ((y : A)⁻¹ * s)⁻¹ = (y : A)⁻¹ * (s * l * s⁻¹) * (y : A) := by group
        _ = (y : A)⁻¹ * ((y : A) * l * (y : A)⁻¹) * (y : A) := by rw [h1]
        _ = l := by group
    have h1 := eq_one_of_centralizes D.e hLn hS hXLS hO2 hcX hc
    have h2 : s = (y : A) := by
      have := congrArg ((y : A) * ·) h1
      simpa using this
    exact hsL (h2 ▸ y.2)
  · exact h

theorem cutsOf_flip_invariant [Finite A] {L X S : Subgroup A} {n : ℕ} (hn : 3 ≤ n)
    (D : BorelIso n L (S ⊓ L)) (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) {s : A}
    (hsS : s ∈ S) (hsL : s ∉ L) {Q : Subgroup A} (hBQ : S ⊓ L ≤ Q)
    (hQn : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) : D.cutsOf Q = flipNodes n (D.cutsOf Q) := by
  have hsN : s ∈ Subgroup.normalizer (L : Set A) := le_normalizer_of_conj_mem hLn (hS.1 hsS)
  have h1 := D.cutsOf_conjSub inf_le_right s hsN
    (autOf_swap hn D hLX hLn hS hXLS hO2 hsS hsL hsN) hBQ
  rwa [conjSub_eq_of_conj_mem hQn hsS] at h1

theorem two_mul_eq_of_flip {n x : ℕ} {I : Set ℕ} (hI : ∀ i ∈ I, IsNode n i)
    (hflip : I = flipNodes n I) (hx : IsNode n x) (hxI : x ∉ I)
    (hu : ∀ y, IsNode n y → y ∉ I → y = x) : 2 * x = n := by
  have h1 : n - x ∉ I := by
    intro h
    have h' : n - x ∈ flipNodes n I := by
      rw [← hflip]
      exact h
    obtain ⟨i, hi, hi'⟩ := h'
    have hin := hI i hi
    have hix : i = x := by
      have := hx.2
      have := hin.2
      omega
    exact hxI (hix ▸ hi)
  have h2 : n - x = x := hu (n - x) (isNode_flip hx) h1
  have := hx.2
  omega

theorem eq_of_unique_missing {n x : ℕ} {I J : Set ℕ} (hI : ∀ i ∈ I, IsNode n i)
    (hJ : ∀ i ∈ J, IsNode n i) (hxI : x ∉ I) (hxJ : x ∉ J)
    (huI : ∀ y, IsNode n y → y ∉ I → y = x) (huJ : ∀ y, IsNode n y → y ∉ J → y = x) : I = J := by
  ext i
  constructor
  · intro hi
    by_contra hiJ
    exact hxI ((huJ i (hI i hi) hiJ) ▸ hi)
  · intro hj
    by_contra hiI
    exact hxJ ((huI i (hJ i hj) hiI) ▸ hj)

end CFSG.Quasithin.FLc
