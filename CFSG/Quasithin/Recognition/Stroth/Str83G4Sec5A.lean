module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP
public import CFSG.Quasithin.Recognition.F112Crit.CoprimeCentralizer
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Delta
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Reduction
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5T

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem mem_normalizer_conjClosure_of {Z K : Subgroup G} {h : G}
    (hZ : h ∈ Subgroup.normalizer (Z : Set G)) (hK : h ∈ Subgroup.normalizer (K : Set G)) :
    h ∈ Subgroup.normalizer (conjClosure Z K : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (K : Set G) → ∀ n ∈ conjClosure Z K,
        g * n * g⁻¹ ∈ conjClosure Z K := by
    intro g hgZ hgK n hn
    have hle : conjClosure Z K ≤ (conjClosure Z K).comap (MulAut.conj g).toMonoidHom := by
      refine conjClosure_le fun k hk z hz => ?_
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : g * (k * z * k⁻¹) * g⁻¹ =
          (g * k * g⁻¹) * (g * z * g⁻¹) * (g * k * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Z K
        ((Subgroup.mem_normalizer_iff.mp hgK k).mp hk)) _).mp
          (le_conjClosure Z K ((Subgroup.mem_normalizer_iff.mp hgZ z).mp hz))
    have h1 := hle hn
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨key h hZ hK n, fun hn => ?_⟩
  have h1 := key h⁻¹ (Subgroup.inv_mem _ hZ) (Subgroup.inv_mem _ hK) _ hn
  rwa [show h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n by group] at h1

private theorem mem_centralizer_conjClosure_iff {Z K : Subgroup G} {f : G} :
    f ∈ Subgroup.centralizer (conjClosure Z K : Set G) ↔
      ∀ g ∈ K, f ∈ Subgroup.centralizer (CFSG.conjugate Z g : Set G) := by
  constructor
  · intro hf g hg
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [SetLike.mem_coe, CFSG.mem_conjugate_iff] at hy
    have hy' : y ∈ conjClosure Z K := by
      have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Z K (K.inv_mem hg))
        (g * y * g⁻¹)).mp (le_conjClosure Z K hy)
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
    exact Subgroup.mem_centralizer_iff.mp hf y hy'
  · intro hf
    have hle : conjClosure Z K ≤ Subgroup.centralizer ({f} : Set G) := by
      refine conjClosure_le fun k hk z hz => ?_
      have hmem : k * z * k⁻¹ ∈ CFSG.conjugate Z k⁻¹ := by
        rw [CFSG.mem_conjugate_iff]
        rwa [show k⁻¹ * (k * z * k⁻¹) * k⁻¹⁻¹ = z by group]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hf k⁻¹ (K.inv_mem hk)) _ hmem)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

private theorem commutator_mem_of_mem_two_subgroup {N I : Subgroup G} (hI : IsPGroup 2 ↥I)
    (hIN : I ≤ Subgroup.normalizer (N : Set G)) {g y : G} (hg : Odd (orderOf g))
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) (hgy : g * y * g⁻¹ * y⁻¹ ∈ I)
    (hgI : ∀ i ∈ I, g * i * g⁻¹ * i⁻¹ ∈ N) : g * y * g⁻¹ * y⁻¹ ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi⟩ : ∃ i, i = g * y * g⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hi] at hgy ⊢
  have hm : g * i * g⁻¹ * i⁻¹ ∈ N := hgI i hgy
  have hpow : ∀ k : ℕ, ∃ n ∈ N, (g * i * g⁻¹ * i⁻¹ * i) ^ k = n * i ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn, hk⟩ := ih
      refine ⟨n * (i ^ k * (g * i * g⁻¹ * i⁻¹) * (i ^ k)⁻¹), N.mul_mem hn
        ((Subgroup.mem_normalizer_iff.mp (hIN (I.pow_mem hgy k)) _).mp hm), ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  have hstep : ∀ k : ℕ, ∃ n ∈ N, g ^ k * y * (g ^ k)⁻¹ = n * i ^ k * y := by
    intro k
    induction k with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨n, hn, hk⟩ := ih
      obtain ⟨m, hmN, hmk⟩ := hpow k
      refine ⟨g * n * g⁻¹ * m, N.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN n).mp hn) hmN, ?_⟩
      have e1 : g * i ^ k * g⁻¹ = (g * i * g⁻¹ * i⁻¹ * i) ^ k := by
        rw [show g * i * g⁻¹ * i⁻¹ * i = g * i * g⁻¹ by group, conj_pow]
      have e2 : g * y * g⁻¹ = i * y := by rw [hi]; group
      calc g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ = g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = (g * n * g⁻¹) * (g * i ^ k * g⁻¹) * (g * y * g⁻¹) := by rw [hk]; group
        _ = (g * n * g⁻¹) * (m * i ^ k) * (i * y) := by rw [e1, hmk, e2]
        _ = g * n * g⁻¹ * m * i ^ (k + 1) * y := by rw [pow_succ]; group
  obtain ⟨n, hn, hr⟩ := hstep (orderOf g)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hr
  have h1 : n * i ^ orderOf g = 1 :=
    calc n * i ^ orderOf g = (n * i ^ orderOf g * y) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [← hr]
      _ = 1 := mul_inv_cancel y
  have h2 : i ^ orderOf g ∈ N := by
    have e : i ^ orderOf g = n⁻¹ * (n * i ^ orderOf g) := by group
    rw [e, h1, mul_one]
    exact N.inv_mem hn
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp hI ⟨i, hgy⟩
  have he' : orderOf i = 2 ^ e := by rw [← he]; exact (Subgroup.orderOf_coe (⟨i, hgy⟩ : ↥I))
  have hcop : (orderOf g).Coprime (orderOf i) := by
    rw [he']
    exact Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hg)
  exact (Subgroup.zpowers_le.mpr h2) (A4.mem_zpowers_pow_of_coprime hcop)

theorem str83G4_mem_z1_of_mem_x_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    {x : G} (hx : x ∈ str83X L1 L2 S)
    (hxN : x ∈ Subgroup.centralizer
      (conjClosure (CFSG.conjugate (str83X L1 L2 S) d.w) (L1 ⊔ S) : Set G)) :
    x ∈ Z1 L1 L2 S := by
  have hfr' := hfr
  obtain ⟨hF, hBS, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hBS ha hSz hL2 hZI
  set X := str83X L1 L2 S with hXdef
  set N₁ := conjClosure (CFSG.conjugate X d.w) (L1 ⊔ S) with hN₁def
  have hLP : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  have hNX : ∀ g ∈ P1 L1 L2 S, ∀ y ∈ X, g * y * g⁻¹ ∈ X := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hg) y).mp hy
  have hZ1X : Z1 L1 L2 S ≤ X := hZ1Z2.trans (z2_le_str83X L1 L2 S)
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hBS (Or.inl ⟨a, ha, hSz⟩)
  have hLZ1 : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [sup_eq_of_S_eq hS1]; exact hZI
  have hXwL : CFSG.conjugate X d.w ≤ L1 ⊔ S :=
    (str83G4_conjugate_x_le_s hfr' d hX).trans le_sup_right
  have hN₁L : N₁ ≤ L1 ⊔ S := conjClosure_le fun g hg z hz =>
    (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem hg (hXwL hz)) ((L1 ⊔ S).inv_mem hg)
  have hZ1N : Z1 L1 L2 S ≤ Subgroup.centralizer (N₁ : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun n hn =>
      (Subgroup.mem_centralizer_iff.mp (hLZ1 (hN₁L hn)) z hz).symm
  let M : Subgroup G := X ⊓ Subgroup.centralizer (N₁ : Set G)
  have hMn : IsNormalIn (L1 ⊔ S) X M := by
    refine ⟨inf_le_left, fun g hg y hy => Subgroup.mem_inf.mpr
      ⟨hNX g (hLP hg) y (Subgroup.mem_inf.mp hy).1, ?_⟩⟩
    exact (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer _
      (le_normalizer_conjClosure _ _ hg)) y).mp (Subgroup.mem_inf.mp hy).2
  rcases hXstep.2.2.2 M hMn (le_inf hZ1X hZ1N) inf_le_left with hMZ | hMX
  · have hxM : x ∈ M := Subgroup.mem_inf.mpr ⟨hx, hxN⟩
    rwa [hMZ] at hxM
  exfalso
  obtain ⟨t, ht, htQ⟩ := SetLike.not_le_iff_exists.mp hB
  have htN : t ∈ N₁ := le_conjClosure _ _ ht
  have hXC : X ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro y hy
    have hyM : y ∈ M := by rw [hMX]; exact hy
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact (Commute.zpow_left
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyM).2 t htN) k).eq
  have hq := str83G4_relIndex_centralizer_x hfr' d hX ht htQ
  rw [Subgroup.relIndex_eq_one.mpr hXC] at hq
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * a + 1) = q at hq h8
  nlinarith

theorem str83G4_mem_centralizer_r
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {c : G}
    (hcX : c ∈ Subgroup.centralizer (str83X L1 L2 S : Set G))
    (hcN : c ∈ Subgroup.centralizer
      (conjClosure (CFSG.conjugate (str83X L1 L2 S) d.w) (L1 ⊔ S) : Set G)) :
    c ∈ Subgroup.centralizer (str83R L1 L2 S : Set G) := by
  have hfr' := hfr
  obtain ⟨hF, hBS, ha, -, hL2, -⟩ := hfr
  set X := str83X L1 L2 S with hXdef
  set N₁ := conjClosure (CFSG.conjugate X d.w) (L1 ⊔ S) with hN₁def
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (bigB_le_normalizer_of_hyp111 hF.1) hBS
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (N₁ : Set G) := by
    rw [d.hBsplit, sup_assoc]
    refine sup_le ((le_sup_right : S ≤ L1 ⊔ S).trans (le_normalizer_conjClosure _ _))
      fun h hh => ?_
    exact mem_normalizer_conjClosure_of ((str83G4_d1_sup_d2_le_normalizer hfr' d).2.1 hh)
      (hBL1 (str83G4Data_sup_le_bigB d hh))
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hBS (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [bigB_comm]
    exact bigB_le_normalizer_of_hyp111 hF.1.symm
  have hQ2NL2 : Q2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (pCoreOf_le 2 (P2 L1 L2 S)).trans (sup_le Subgroup.le_normalizer hBL2)
  have hwinv : d.w⁻¹ ∈ L2 ⊔ Q2 L1 L2 S := by
    rw [← sup_eq_of_S_eq_right hS2]
    exact (L2 ⊔ S).inv_mem d.hwH2
  obtain ⟨g₀, hg₀, q, hq, hwq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2NL2).mp hwinv
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hg₀B : g₀ ∉ bigB L1 L2 S := by
    intro hg
    apply d.hwNotN
    have hw : d.w⁻¹ ∈ bigB L1 L2 S := by
      rw [hwq]
      exact (bigB L1 L2 S).mul_mem hg (hSB (hQ2S hq))
    have h := hBS ((bigB L1 L2 S).inv_mem hw)
    rwa [inv_inv] at h
  have hQ2P1 : q⁻¹ ∈ P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (hSB (hQ2S ((Q2 L1 L2 S).inv_mem hq)))
  have hRle : str83R L1 L2 S ≤ Subgroup.centralizer ({c} : Set G) := by
    refine conjClosure_le fun p hp z hz => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rcases mem_bigB_or_mem_doubleCoset_p2 (n := 2 * a + 1) (by omega) hF hL2 hg₀ hg₀B hp with
      hpB | hpB
    · have hpz : p * z * p⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S
        ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hpB)) z).mp hz
      exact Subgroup.mem_centralizer_iff.mp hcX _ hpz
    · obtain ⟨x₁, hx₁, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hpB
      obtain ⟨b₁, hb₁, y, hy, rfl⟩ := Set.mem_mul.mp hx₁
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hz1 : b₂ * z * b₂⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S
        ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hb₂)) z).mp hz
      have hz2 : q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hQ2P1) _).mp hz1
      have hyw : d.w⁻¹ * (q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹) * d.w ∈ CFSG.conjugate X d.w := by
        rw [CFSG.mem_conjugate_iff]
        rwa [show d.w * (d.w⁻¹ * (q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹) * d.w) * d.w⁻¹ =
          q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹ by group]
      have hyN : b₁ * (d.w⁻¹ * (q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹) * d.w) * b₁⁻¹ ∈ N₁ :=
        (Subgroup.mem_normalizer_iff.mp (hBN hb₁) _).mp (le_conjClosure _ _ hyw)
      have hg₀eq : g₀ = d.w⁻¹ * q⁻¹ := by rw [hwq]; group
      have e : b₁ * g₀ * b₂ * z * (b₁ * g₀ * b₂)⁻¹ =
          b₁ * (d.w⁻¹ * (q⁻¹ * (b₂ * z * b₂⁻¹) * q⁻¹⁻¹) * d.w) * b₁⁻¹ := by
        rw [hg₀eq]; group
      rw [e]
      exact Subgroup.mem_centralizer_iff.mp hcN _ hyN
  exact Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRle hr)

theorem str83G4_commutator_mem_z2_of_mem_oTwoUpper
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    {g : G} (hg : g ∈ oTwoUpper (L2 ⊔ S)) :
    ∀ y ∈ Q2 L1 L2 S ⊓ Subgroup.centralizer (str83R L1 L2 S : Set G),
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S := by
  have hfr' := hfr
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  set YR := Q2 L1 L2 S ⊓ Subgroup.centralizer (str83R L1 L2 S : Set G) with hYRdef
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hNZ2 : ∀ g ∈ P2 L1 L2 S, ∀ z ∈ Z2 L1 L2 S, g * z * g⁻¹ ∈ Z2 L1 L2 S := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hg) z).mp hz
  have hNYR : ∀ g ∈ P2 L1 L2 S, ∀ y ∈ YR, g * y * g⁻¹ ∈ YR := by
    intro g hg y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) hg) y).mp hyQ, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer _
      (le_normalizer_str83R L1 L2 S hg)) y).mp hyC
  have hXR : X ≤ str83R L1 L2 S := le_conjClosure _ _
  have hXwR : Xw ≤ str83R L1 L2 S := by
    intro x hx
    rw [hXwdef, CFSG.mem_conjugate_iff] at hx
    have hwP : d.w⁻¹ ∈ P2 L1 L2 S := (P2 L1 L2 S).inv_mem (hL2P d.hwH2)
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83R L1 L2 S hwP) _).mp (hXR hx)
    rwa [show d.w⁻¹ * (d.w * x * d.w⁻¹) * d.w⁻¹⁻¹ = x by group] at h
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  have hYRY0 : YR ≤ str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) := by
    intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyCX : y ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXR) hyC
    have hyQ1 : y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
      str83G4_centralizer_x_le hfr' (str83G4_not_le_normalizer_z2 hfr')
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (hQ2S hyQ), hyCX⟩)
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hyQ1).1, hyCX⟩,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXwR) hyC⟩
  have hI2 : IsPGroup 2 ↥(X ⊓ Xw) :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le (inf_le_left.trans (str83X_le_q1 hfr'))
  have hINZ2 : X ⊓ Xw ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := fun i hi =>
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) (hL2P (Subgroup.mem_sup_right
      ((str83G4_q1_le_s hfr') (str83X_le_q1 hfr' (Subgroup.mem_inf.mp hi).1))))
  have hD2L : ∀ δ ∈ d.D2, δ ∈ L2 ⊔ S := fun δ hδ =>
    Subgroup.mem_sup_left ((F1.borelOf_le L2 S) (d.hD2hall.1 hδ))
  have hD2 : ∀ δ ∈ d.D2, ∀ y ∈ YR, δ * y * δ⁻¹ * y⁻¹ ∈ Z2 L1 L2 S := by
    intro δ hδ y hy
    have hδodd : Odd (orderOf δ) :=
      Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hδ)
    exact commutator_mem_of_mem_two_subgroup hI2 hINZ2 hδodd
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) (hL2P (hD2L δ hδ)))
      (hY5 δ (Subgroup.mem_sup_right hδ) y (hYRY0 hy)) (hIL2 δ (hD2L δ hδ))
  let K : Subgroup G :=
    { carrier := {k | k ∈ L2 ⊔ S ∧ ∀ y ∈ YR, k * y * k⁻¹ * y⁻¹ ∈ Z2 L1 L2 S}
      mul_mem' := by
        rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
        refine ⟨(L2 ⊔ S).mul_mem hk₁ hk₂, fun y hy => ?_⟩
        have e : k₁ * k₂ * y * (k₁ * k₂)⁻¹ * y⁻¹ =
            k₁ * (k₂ * y * k₂⁻¹ * y⁻¹) * k₁⁻¹ * (k₁ * y * k₁⁻¹ * y⁻¹) := by
          group
        rw [e]
        exact (Z2 L1 L2 S).mul_mem (hNZ2 k₁ (hL2P hk₁) _ (h₂ y hy)) (h₁ y hy)
      one_mem' := ⟨(L2 ⊔ S).one_mem, fun y _ => by
        rw [show (1 : G) * y * 1⁻¹ * y⁻¹ = 1 by group]
        exact (Z2 L1 L2 S).one_mem⟩
      inv_mem' := by
        rintro k ⟨hk, h⟩
        refine ⟨(L2 ⊔ S).inv_mem hk, fun y hy => ?_⟩
        have h1 := h _ (hNYR _ (hL2P ((L2 ⊔ S).inv_mem hk)) y hy)
        have e : k⁻¹ * y * k⁻¹⁻¹ * y⁻¹ =
            (k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ * (k⁻¹ * y * k⁻¹⁻¹)⁻¹)⁻¹ := by
          group
        rw [e]
        exact (Z2 L1 L2 S).inv_mem h1 }
  have hKmem : ∀ k, k ∈ K ↔ k ∈ L2 ⊔ S ∧ ∀ y ∈ YR, k * y * k⁻¹ * y⁻¹ ∈ Z2 L1 L2 S :=
    fun _ => Iff.rfl
  have hKL : K ≤ L2 ⊔ S := fun k hk => ((hKmem k).mp hk).1
  have key : ∀ l ∈ L2 ⊔ S, ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
    intro l hl k hk
    obtain ⟨hkL, hk'⟩ := (hKmem k).mp hk
    refine (hKmem _).mpr ⟨(L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hl hkL) ((L2 ⊔ S).inv_mem hl),
      fun y hy => ?_⟩
    have h1 := hNZ2 l (hL2P hl) _ (hk' _ (hNYR _ (hL2P ((L2 ⊔ S).inv_mem hl)) y hy))
    have e : l * k * l⁻¹ * y * (l * k * l⁻¹)⁻¹ * y⁻¹ =
        l * (k * (l⁻¹ * y * l⁻¹⁻¹) * k⁻¹ * (l⁻¹ * y * l⁻¹⁻¹)⁻¹) * l⁻¹ := by
      group
    rw [e]
    exact h1
  have hKN : L2 ⊔ S ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => key l hl k hk, fun hk => ?_⟩
    have h := key l⁻¹ ((L2 ⊔ S).inv_mem hl) _ hk
    rwa [show l⁻¹ * (l * k * l⁻¹) * l⁻¹⁻¹ = k by group] at h
  have hKQ : ¬ K ≤ Q2 L1 L2 S := by
    intro hle
    obtain ⟨x, hx, hx1⟩ :=
      (Subgroup.bot_or_exists_ne_one d.D2).resolve_left (str83G4Data_D2_ne_bot hfr' d)
    have hbot : d.D2 ⊓ Q2 L1 L2 S = ⊥ := by
      rw [inf_comm]
      exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P2 L1 L2 S)) d.hD2hall.2.1
    have hmem : x ∈ d.D2 ⊓ Q2 L1 L2 S :=
      Subgroup.mem_inf.mpr ⟨hx, hle ((hKmem x).mpr ⟨hD2L x hx, hD2 x hx⟩)⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hle : oTwoUpper (L2 ⊔ S) ≤ K := (Subgroup.closure_le K).mpr fun x hx =>
    str83G4_mem_of_normal_right hfr' hKL hKN hKQ hx.1 hx.2
  exact ((hKmem g).mp (hle hg)).2

theorem str83G4_commute_odd_right
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    {c : G} (hcY : c ∈ str83Y L1 L2 S)
    (hcN : c ∈ Subgroup.centralizer
      (conjClosure (CFSG.conjugate (str83X L1 L2 S) d.w) (L1 ⊔ S) : Set G))
    (hcH : ∀ h ∈ d.D1 ⊔ d.D2, c * h = h * c) :
    ∀ g ∈ L2 ⊔ S, Odd (orderOf g) → c * g = g * c := by
  have hfr' := hfr
  obtain ⟨hF, hBS, -, -, -, -⟩ := hfr
  set X := str83X L1 L2 S with hXdef
  set N₁ := conjClosure (CFSG.conjugate X d.w) (L1 ⊔ S) with hN₁def
  set L0 := oTwoUpper (L2 ⊔ S) with hL0def
  have hcX : c ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hcY).2
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hL0L : L0 ≤ L2 ⊔ S := oTwoUpper_le _
  have hQ2CZ2 : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le _
  have hZ2comm : ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hQ2CZ2 (hZ2Q2 hy)) x hx
  have hNZ2 : ∀ g ∈ P2 L1 L2 S, ∀ z ∈ Z2 L1 L2 S, g * z * g⁻¹ ∈ Z2 L1 L2 S := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hg) z).mp hz
  have hcQ2 : c ∈ Q2 L1 L2 S :=
    (Subgroup.mem_inf.mp (str83G4_centralizer_x_le hfr' (str83G4_not_le_normalizer_z2 hfr')
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right
        (str83G4_q1_le_s hfr' (Subgroup.mem_inf.mp hcY).1), hcX⟩))).2
  have hcYR : c ∈ Q2 L1 L2 S ⊓ Subgroup.centralizer (str83R L1 L2 S : Set G) :=
    Subgroup.mem_inf.mpr ⟨hcQ2, str83G4_mem_centralizer_r hfr' d hcX hcN⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : G → G, ∀ g, κ g = g * c * g⁻¹ * c⁻¹ := ⟨_, fun _ => rfl⟩
  have hκZ2 : ∀ g ∈ L0, κ g ∈ Z2 L1 L2 S := fun g hg => by
    rw [hκ]
    exact str83G4_commutator_mem_z2_of_mem_oTwoUpper hfr' d hY5 hIL2 hg c hcYR
  have hequiv : ∀ l ∈ L0, ∀ u ∈ L0, u ∈ Q2 L1 L2 S → κ (l * u * l⁻¹) = l * κ u * l⁻¹ := by
    intro l hl u hu huQ
    have hal : l⁻¹ * κ l * l ∈ Z2 L1 L2 S := by
      have h := hNZ2 l⁻¹ (hL2P (hL0L (L0.inv_mem hl))) _ (hκZ2 l hl)
      rwa [inv_inv] at h
    have e : κ (l * u * l⁻¹) =
        l * ((u * (l⁻¹ * κ l * l)⁻¹ * u⁻¹) * κ u * (l⁻¹ * κ l * l)) * l⁻¹ := by
      simp only [hκ]; group
    have hcomm1 : u * (l⁻¹ * κ l * l)⁻¹ * u⁻¹ = (l⁻¹ * κ l * l)⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp (hQ2CZ2 huQ) _ ((Z2 L1 L2 S).inv_mem hal)
      rw [← h]; group
    rw [e, hcomm1, hZ2comm _ ((Z2 L1 L2 S).inv_mem hal) _ (hκZ2 u hu)]
    group
  have hκZ1 : ∀ u ∈ L0, u ∈ Q2 L1 L2 S → κ u ∈ Z1 L1 L2 S := by
    intro u hu huQ
    have h1 : u * c * u⁻¹ ∈ Subgroup.centralizer (N₁ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer _
        (le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right (hQ2S huQ)))) c).mp hcN
    have h2 : κ u ∈ Subgroup.centralizer (N₁ : Set G) := by
      rw [hκ]; exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcN)
    exact str83G4_mem_z1_of_mem_x_centralizer hfr' d hX hB hXstep
      (z2_le_str83X L1 L2 S (hκZ2 u hu)) h2
  have hQ2NL0 : Q2 L1 L2 S ≤ Subgroup.normalizer (L0 : Set G) :=
    (hQ2S.trans le_sup_right).trans (CFSG.Quasithin.le_normalizer_oTwoUpper _)
  have hw : d.w ∈ L0 ⊔ Q2 L1 L2 S := by
    rw [hL0def, str83G4_oTwoUpper_sup_right hfr' d]; exact d.hwH2
  obtain ⟨l₀, hl₀, s₀, hs₀, hws⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ2NL0).mp hw
  have hκ1 : ∀ u ∈ L0, u ∈ Q2 L1 L2 S → κ u = 1 := by
    intro u hu huQ
    have hu' : l₀ * u * l₀⁻¹ ∈ L0 := L0.mul_mem (L0.mul_mem hl₀ hu) (L0.inv_mem hl₀)
    have huQ' : l₀ * u * l₀⁻¹ ∈ Q2 L1 L2 S := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) (hL2P (hL0L hl₀))) u).mp huQ
    have hz2 := hκZ1 _ hu' huQ'
    rw [hequiv l₀ hl₀ u hu huQ] at hz2
    have hs : s₀ * κ u * s₀⁻¹ = κ u := by
      have h := Subgroup.mem_centralizer_iff.mp (hQ2CZ2 hs₀) _ (hκZ2 u hu)
      rw [← h]; group
    have hmem : κ u ∈ CFSG.conjugate (Z1 L1 L2 S) d.w := by
      rw [CFSG.mem_conjugate_iff, hws,
        show l₀ * s₀ * κ u * (l₀ * s₀)⁻¹ = l₀ * (s₀ * κ u * s₀⁻¹) * l₀⁻¹ by group, hs]
      exact hz2
    have h := Subgroup.mem_inf.mpr ⟨hκZ1 u hu huQ, hmem⟩
    rw [str83G4_z1_inf_conjugate_w hfr' d] at h
    exact Subgroup.mem_bot.mp h
  obtain ⟨x, hx, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D1).resolve_left (str83G4Data_D1_ne_bot hfr' d)
  obtain ⟨δ, hδ, hxδ⟩ := str83G4_exists_delta_two hfr' d hx
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    refine hx1 (hδ₂ x hx fun l hl => ?_)
    have h := hxδ l hl
    rwa [inv_one, mul_one] at h
  have hkH : x * δ⁻¹ ∈ d.D1 ⊔ d.D2 :=
    (d.D1 ⊔ d.D2).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (d.D2.inv_mem hδ))
  have hkB : x * δ⁻¹ ∈ bigB L1 L2 S := str83G4Data_sup_le_bigB d hkH
  have hkQ := str83G4_trivial_on_sup_right hfr' hkB hxδ
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [bigB_comm]
    exact bigB_le_normalizer_of_hyp111 hF.1.symm
  have hkN : x * δ⁻¹ ∈ Subgroup.normalizer (L0 : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_oTwoUpper (L2 ⊔ S)
      (F1.le_normalizer_sup hBL2 hBS hkB)
  have hch : c * (x * δ⁻¹) = (x * δ⁻¹) * c := hcH _ hkH
  intro g hg hodd
  have hgL0 : g ∈ L0 := mem_oTwoUpper_of_odd hg hodd
  have hu : x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹ ∈ L0 :=
    L0.mul_mem ((Subgroup.mem_normalizer_iff.mp hkN g).mp hgL0) (L0.inv_mem hgL0)
  have huQ := hkQ g hg
  have hκu := hκ1 _ hu huQ
  have hc' : (x * δ⁻¹)⁻¹ * c * (x * δ⁻¹) = c := by rw [mul_assoc, hch]; group
  have hc'' : (x * δ⁻¹)⁻¹ * c⁻¹ = c⁻¹ * (x * δ⁻¹)⁻¹ := by
    rw [← mul_inv_rev, hch, mul_inv_rev]
  have e1 : κ (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹) = (x * δ⁻¹) * κ g * (x * δ⁻¹)⁻¹ := by
    simp only [hκ]
    calc x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * c * (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹)⁻¹ * c⁻¹
        = x * δ⁻¹ * g * ((x * δ⁻¹)⁻¹ * c * (x * δ⁻¹)) * g⁻¹ * ((x * δ⁻¹)⁻¹ * c⁻¹) := by group
      _ = x * δ⁻¹ * (g * c * g⁻¹ * c⁻¹) * (x * δ⁻¹)⁻¹ := by rw [hc', hc'']; group
  have e2 : κ (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹) =
      (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹) * κ g * (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹)⁻¹ *
        κ (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹) := by
    simp only [hκ]; group
  rw [hκu, mul_one] at e2
  have e3 : (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹) * κ g * (x * δ⁻¹ * g * (x * δ⁻¹)⁻¹ * g⁻¹)⁻¹ =
      κ g := by
    have h := Subgroup.mem_centralizer_iff.mp (hQ2CZ2 huQ) _ (hκZ2 g hgL0)
    rw [← h]; group
  have hfix : (x * δ⁻¹) * κ g * (x * δ⁻¹)⁻¹ = κ g := by rw [← e1, e2, e3]
  have hk1 := str83G4_eq_one_of_fix_z2 hfr' d hZ2 hx hδ hδ1 hxδ (hκZ2 g hgL0) hfix
  rw [hκ] at hk1
  calc c * g = (g * c * g⁻¹ * c⁻¹)⁻¹ * (g * c) := by group
    _ = g * c := by rw [hk1, inv_one, one_mul]

theorem str83G4_mem_z1_of_forall_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    {f : G} (hf : f ∈ str83Y L1 L2 S)
    (hfN : ∀ g ∈ L1 ⊔ S, f ∈ Subgroup.centralizer
      (CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) g : Set G)) :
    f ∈ Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hBS, ha, hSz, hL2, hZI⟩ := hfr
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  set N₁ := conjClosure Xw (L1 ⊔ S) with hN₁def
  set YN := str83Y L1 L2 S ⊓ Subgroup.centralizer (N₁ : Set G) with hYNdef
  have hfC : f ∈ Subgroup.centralizer (N₁ : Set G) := mem_centralizer_conjClosure_iff.mpr hfN
  have hfYN : f ∈ YN := Subgroup.mem_inf.mpr ⟨hf, hfC⟩
  have hHP : d.D1 ⊔ d.D2 ≤ P1 L1 L2 S :=
    (str83G4Data_sup_le_bigB d).trans (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer ((L1 ⊔ S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (bigB_le_normalizer_of_hyp111 hF.1) hBS
  have hHN₁ : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (N₁ : Set G) := fun h hh =>
    mem_normalizer_conjClosure_of ((str83G4_d1_sup_d2_le_normalizer hfr' d).2.1 hh)
      (hBL1 (str83G4Data_sup_le_bigB d hh))
  have hHYN : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (YN : Set G) := fun h hh =>
    A4.mem_normalizer_inf (A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hHP hh))
      (F7.normalizer_le_normalizer_centralizer _ (le_normalizer_str83X L1 L2 S (hHP hh))))
      (F7.normalizer_le_normalizer_centralizer _ (hHN₁ hh))
  have hHZ1 : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := fun h hh =>
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S) (hHP hh)
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hBS (Or.inl ⟨a, ha, hSz⟩)
  have hLZ1 : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [sup_eq_of_S_eq hS1]; exact hZI
  have hXwL : Xw ≤ L1 ⊔ S := (str83G4_conjugate_x_le_s hfr' d hX).trans le_sup_right
  have hN₁L : N₁ ≤ L1 ⊔ S := conjClosure_le fun g hg z hz =>
    (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem hg (hXwL hz)) ((L1 ⊔ S).inv_mem hg)
  have hZ1YN : Z1 L1 L2 S ≤ YN := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨omegaOneCenterOf_le _ hz,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, Subgroup.mem_centralizer_iff.mpr
        fun n hn => (Subgroup.mem_centralizer_iff.mp (hLZ1 (hN₁L hn)) z hz).symm⟩
    exact (Subgroup.mem_centralizer_iff.mp (Q1_le_centralizer_Z1 L1 L2 S
      (str83X_le_q1 hfr' hy)) z hz).symm
  have hYN2 : IsPGroup 2 ↥YN :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le (inf_le_left.trans inf_le_left)
  have hcomm : ∀ h ∈ d.D1 ⊔ d.D2, f * h * f⁻¹ * h⁻¹ ∈ Z1 L1 L2 S := by
    intro h hh
    have hfY0 : f ∈ str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) :=
      Subgroup.mem_inf.mpr ⟨hf, Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (le_conjClosure Xw (L1 ⊔ S))) hfC⟩
    have hI := hY5 h hh f hfY0
    have hYN' : h * f * h⁻¹ * f⁻¹ ∈ YN :=
      YN.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHYN hh) f).mp hfYN) (YN.inv_mem hfYN)
    have hz := str83G4_mem_z1_of_mem_x_centralizer hfr' d hX hB hXstep
      (Subgroup.mem_inf.mp hI).1 (Subgroup.mem_inf.mp hYN').2
    rw [show f * h * f⁻¹ * h⁻¹ = (h * f * h⁻¹ * f⁻¹)⁻¹ by group]
    exact (Z1 L1 L2 S).inv_mem hz
  obtain ⟨n, hn, c, hc, hcH, rfl⟩ := F112Crit.exists_mul_centralizer_of_comm_mem hYN2
    (str83G4Data_odd_card_sup d) hZ1YN hHYN hHZ1 hfYN hcomm
  obtain ⟨hcY, hcC⟩ := Subgroup.mem_inf.mp hc
  have hN₁Q : ¬ N₁ ≤ Q1 L1 L2 S := fun hle => hB ((le_conjClosure Xw (L1 ⊔ S)).trans hle)
  have h1 : ∀ g ∈ L1 ⊔ S, Odd (orderOf g) → c * g = g * c := fun g hg hodd =>
    (Subgroup.mem_centralizer_iff.mp hcC g (str83G4_mem_of_normal_left hfr' hN₁L
      (le_normalizer_conjClosure _ _) hN₁Q hg hodd)).symm
  have h2 := str83G4_commute_odd_right hfr' d hX hB hY5 hZ2 hδ₂ hXstep hIL2 hcY hcC hcH
  rw [str83G4_eq_one_of_commute_odd hfr' d (str83G4_q1_le_s hfr' (Subgroup.mem_inf.mp hcY).1)
    h1 h2, mul_one]
  exact hn

end CFSG.Quasithin.Stroth

end
