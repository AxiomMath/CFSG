module

public import CFSG.Quasithin.Background.G2L2
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
open scoped MatrixGroups Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem eq_bot_of_central_two_subgroup_splits {Y : Type*} [Group Y] [Finite Y] {Z C : Subgroup Y}
    (hcomm : ∀ z ∈ Z, ∀ y : Y, y * z = z * y) (hZ2 : IsPGroup 2 Z) (hdisj : Z ⊓ C = ⊥)
    (hodd : ¬ 2 ∣ (Z ⊔ C).index) (hperf : ∀ (f : Y →* Z) (y : Y), f y = 1) : Z = ⊥ := by
  classical
  have hc : ∀ (m : Z) (n : C), Commute (Z.subtype m) (C.subtype n) :=
    fun m n => (hcomm m m.2 n).symm
  let φ : ↥Z × ↥C →* Y := Z.subtype.noncommCoprod C.subtype hc
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hdisj
  have hrange : φ.range = Z ⊔ C := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  let e : ↥Z × ↥C ≃* φ.range := MonoidHom.ofInjective hinj
  have hZM : ∀ z : Z, (z : Y) ∈ φ.range := fun z => ⟨(z, 1), by simp [φ]⟩
  let ρ : φ.range →* Z := (MonoidHom.fst Z C).comp e.symm.toMonoidHom
  have hρ : ∀ z : Z, ρ ⟨z, hZM z⟩ = z := by
    intro z
    have h1 : e (z, 1) = ⟨z, hZM z⟩ := Subtype.ext (show φ (z, 1) = z by simp [φ])
    have h2 : e.symm ⟨z, hZM z⟩ = (z, 1) := by rw [← h1]; exact e.symm_apply_apply _
    simp [ρ, h2]
  have : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext (hcomm b b.2 a)⟩⟩
  have key : ∀ z : Z, ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * (z : Y) ^ k * g₀ ∈ φ.range →
      g₀⁻¹ * (z : Y) ^ k * g₀ = (z : Y) ^ k := by
    intro z k g₀ _
    have h := hcomm ((z : Y) ^ k) (Z.pow_mem z.2 k) g₀⁻¹
    rw [h, mul_assoc, inv_mul_cancel, mul_one]
  have htr : ∀ z : Z, MonoidHom.transfer ρ (z : Y) = z ^ (φ.range).index := by
    intro z
    rw [MonoidHom.transfer_eq_pow ρ (z : Y) (key z)]
    exact hρ (z ^ (φ.range).index)
  rw [eq_bot_iff]
  intro z hz
  have h1 := htr ⟨z, hz⟩
  rw [hperf (MonoidHom.transfer ρ) _] at h1
  obtain ⟨k, hk⟩ := hZ2 ⟨z, hz⟩
  rw [hrange] at h1
  have hcop : Nat.Coprime (2 ^ k) (Z ⊔ C).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h2 : (⟨z, hz⟩ : Z) ^ (2 ^ k).gcd (Z ⊔ C).index = 1 := pow_gcd_eq_one.2 ⟨hk, h1.symm⟩
  rw [hcop, pow_one] at h2
  have := congrArg Subtype.val h2
  simpa using this


theorem le_of_central_modulo_two_splitting {Γ : Type*} [Group Γ] [Finite Γ] {B K C : Subgroup Γ}
    [B.Normal] (hBK : B ≤ K) (hcent : ∀ k ∈ K, ∀ y : Γ, k * y * k⁻¹ * y⁻¹ ∈ B)
    (hK2 : IsPGroup 2 K) (hKC : K ⊓ C ≤ B) (hodd : ¬ 2 ∣ (K ⊔ C).index)
    (hperf : ∀ N : Subgroup Γ, N.Normal → (∀ x : Γ, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = ⊤) :
    K ≤ B := by
  classical
  let q : Γ →* Γ ⧸ B := QuotientGroup.mk' B
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective B
  have hker : q.ker = B := QuotientGroup.ker_mk' B
  have hZ2 : IsPGroup 2 (K.map q) := hK2.map q
  have hZ : K.map q = ⊥ := by
    refine eq_bot_of_central_two_subgroup_splits (C := C.map q) ?_ hZ2 ?_ ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩ y
      obtain ⟨γ, rfl⟩ := hq y
      show (QuotientGroup.mk γ : Γ ⧸ B) * QuotientGroup.mk k = QuotientGroup.mk k * QuotientGroup.mk γ
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have := hcent k⁻¹ (K.inv_mem hk) γ⁻¹
      simp only [inv_inv] at this
      simpa [mul_assoc] using this
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨k, hk, rfl⟩ := hx1
      obtain ⟨c, hc, hck⟩ := hx2
      have h1 : c⁻¹ * k ∈ B := QuotientGroup.eq.1 hck
      have h2 : c ∈ K := by
        have h3 : c⁻¹ ∈ K := by
          have := K.mul_mem (hBK h1) (K.inv_mem hk)
          simpa using this
        simpa using K.inv_mem h3
      have h4 : c ∈ B := hKC ⟨h2, hc⟩
      have h5 : q c = 1 := (QuotientGroup.eq_one_iff c).2 h4
      rw [← hck, h5]
      exact Subgroup.one_mem _
    · rw [← Subgroup.map_sup]
      have := Subgroup.index_map (K ⊔ C) q
      rw [hker, sup_eq_left.2 (hBK.trans le_sup_left), MonoidHom.range_eq_top.2 hq,
        Subgroup.index_top, mul_one] at this
      rw [this]
      exact hodd
    · intro f y
      obtain ⟨γ, rfl⟩ := hq y
      have hN : (f.comp q).ker = ⊤ := by
        refine hperf _ (MonoidHom.normal_ker _) fun x => ?_
        obtain ⟨k, hk⟩ := hZ2 (f (q x))
        refine ⟨k, ?_⟩
        rw [MonoidHom.mem_ker]
        simpa [map_pow] using hk
      have : γ ∈ (f.comp q).ker := by rw [hN]; trivial
      exact this
  intro k hk
  have h1 : q k ∈ K.map q := Subgroup.mem_map_of_mem q hk
  rw [hZ, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff k).1 h1

section Three

variable {U Sx I : Subgroup G} {g : G}

theorem comm_mem_inf_of_normalizes {u s : G} (hu : u ∈ U) (hs : s ∈ Sx)
    (hUSx : ∀ x ∈ U, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx) (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    u * s * u⁻¹ * s⁻¹ ∈ U ⊓ Sx := by
  refine ⟨?_, ?_⟩
  · have h1 : s * u⁻¹ * s⁻¹ ∈ U := hSxU s hs u⁻¹ (U.inv_mem hu)
    have := U.mul_mem hu h1
    simpa [mul_assoc] using this
  · exact Sx.mul_mem (hUSx u hu s hs) (Sx.inv_mem hs)

theorem rconj_inf_le_Sx (hgI : g ∈ I) (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx) :
    rconj (U ⊓ Sx) g ≤ Sx := by
  intro y hy
  rw [mem_rconj] at hy
  have h := hINorm g⁻¹ (I.inv_mem hgI) _ hy.2
  simpa [mul_assoc] using h

theorem comm_mem_rconj_inf (hgI : g ∈ I) (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hUI : U ≤ I) (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) {u s : G}
    (hu : u ∈ rconj U g) (hs : s ∈ Sx) : u * s * u⁻¹ * s⁻¹ ∈ rconj (U ⊓ Sx) g := by
  rw [mem_rconj] at hu ⊢
  have hs' : g * s * g⁻¹ ∈ Sx := hINorm g hgI s hs
  have h := comm_mem_inf_of_normalizes hu hs' (fun x hx y hy => hINorm x (hUI hx) y hy) hSxU
  have e : g * (u * s * u⁻¹ * s⁻¹) * g⁻¹ =
      (g * u * g⁻¹) * (g * s * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * s * g⁻¹)⁻¹ := by group
  rwa [e]

theorem I_le_normalizer_P (hI : I = U ⊔ rconj U g) (hgI : g ∈ I)
    (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    I ≤ Subgroup.normalizer ((U ⊓ Sx ⊔ rconj (U ⊓ Sx) g : Subgroup G) : Set G) := by
  have hUI : U ≤ I := hI ▸ le_sup_left
  have hPSx : U ⊓ Sx ⊔ rconj (U ⊓ Sx) g ≤ Sx := sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)
  rw [hI]
  refine sup_le (le_normalizer_of_conj_mem fun u hu y hy => ?_)
    (le_normalizer_of_conj_mem fun u hu y hy => ?_)
  · have h := comm_mem_inf_of_normalizes hu (hPSx hy)
      (fun x hx s hs => hINorm x (hUI hx) s hs) hSxU
    have h' : u * y * u⁻¹ * y⁻¹ ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g :=
      (le_sup_left : U ⊓ Sx ≤ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g) h
    have := Subgroup.mul_mem _ h' hy
    simpa [mul_assoc] using this
  · have h := comm_mem_rconj_inf hgI hINorm hUI hSxU hu (hPSx hy)
    have h' : u * y * u⁻¹ * y⁻¹ ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g :=
      (le_sup_right : rconj (U ⊓ Sx) g ≤ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g) h
    have := Subgroup.mul_mem _ h' hy
    simpa [mul_assoc] using this

theorem comm_Sx_mem_P (hI : I = U ⊔ rconj U g) (hgI : g ∈ I)
    (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) {x s : G} (hx : x ∈ I) (hs : s ∈ Sx) :
    x * s * x⁻¹ * s⁻¹ ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g := by
  have hIP := I_le_normalizer_P hI hgI hINorm hSxU
  have hUI : U ≤ I := hI ▸ le_sup_left
  have hx' : x ∈ U ⊔ rconj U g := hI ▸ hx
  clear hx
  rw [Subgroup.sup_eq_closure] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact (le_sup_left : U ⊓ Sx ≤ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g)
        (comm_mem_inf_of_normalizes hy hs (fun x hx s hs => hINorm x (hUI hx) s hs) hSxU)
    · exact (le_sup_right : rconj (U ⊓ Sx) g ≤ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g)
        (comm_mem_rconj_inf hgI hINorm hUI hSxU hy hs)
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyI : y ∈ I := by
      rw [hI, Subgroup.sup_eq_closure]; exact hy
    have h1 : y * (z * s * z⁻¹ * s⁻¹) * y⁻¹ ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g :=
      (Subgroup.mem_normalizer_iff.1 (hIP hyI) _).1 ihz
    have : y * z * s * (y * z)⁻¹ * s⁻¹ =
        (y * (z * s * z⁻¹ * s⁻¹) * y⁻¹) * (y * s * y⁻¹ * s⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h1 ihy
  | inv y hy ih =>
    have hyI : y ∈ I := by
      rw [hI, Subgroup.sup_eq_closure]; exact hy
    have h1 : y⁻¹ * (y * s * y⁻¹ * s⁻¹)⁻¹ * y ∈ U ⊓ Sx ⊔ rconj (U ⊓ Sx) g := by
      have := (Subgroup.mem_normalizer_iff.1 (hIP (I.inv_mem hyI)) _).1 (Subgroup.inv_mem _ ih)
      simpa [mul_assoc] using this
    have : y⁻¹ * s * y⁻¹⁻¹ * s⁻¹ = y⁻¹ * (y * s * y⁻¹ * s⁻¹)⁻¹ * y := by group
    rw [this]
    exact h1

theorem W_le_normalizer_rconj (hgI : g ∈ I) (hINorm : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx)
    (hUI : U ≤ I) (hSxU : ∀ y ∈ Sx, ∀ x ∈ U, y * x * y⁻¹ ∈ U) :
    U ⊓ Sx ≤ Subgroup.normalizer (rconj (U ⊓ Sx) g : Set G) := by
  refine le_normalizer_of_conj_mem fun w hw y hy => ?_
  have hyU : y ∈ rconj U g := by
    have := (Subgroup.mem_inf.1 (mem_rconj.1 hy)).1
    exact mem_rconj.2 this
  have h := comm_mem_rconj_inf hgI hINorm hUI hSxU hyU hw.2
  have e : w * y * w⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h) hy

end Three

theorem zpowers_c3_inf_Rg {F : Type*} [Field F] [CharP F 2] {A : SL(2, F)}
    (h1 : A ∈ Subgroup.zpowers (c3 F)) (h2 : A ∈ Rg F) : A = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h1
  obtain ⟨b, hb⟩ := mem_Rg.1 h2
  have h3 : (c3 F ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c3_pow_three, one_zpow]
  have h4 : (c3 F ^ k) ^ 2 = 1 := by
    rw [← hb, pow_two]
    exact e12_mul_self b
  calc c3 F ^ k = (c3 F ^ k) ^ 3 * ((c3 F ^ k) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h4]; simp

theorem eq_top_of_oTwoUpper_eq {L : Subgroup G} (h : L = oTwoUpper L) (N : Subgroup ↥L)
    (hN : ∀ x : ↥L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = ⊤ := by
  have h1 : oTwoUpper L ≤ N.map L.subtype := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, hk⟩ := hN ⟨x, hx⟩
    exact ⟨k, ⟨x, hx⟩ ^ 2 ^ k, hk, by simp⟩
  rw [eq_top_iff]
  intro x _
  have h2 : (x : G) ∈ N.map L.subtype := h1 (h ▸ x.2)
  obtain ⟨y, hy, hyx⟩ := h2
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem mem_pCoreOf_of_mem_pCoreOf_of_le [Finite G] {I M : Subgroup G} (hIM : I ≤ M) {x : G}
    (hx : x ∈ I) (hxO : x ∈ pCoreOf 2 M) : x ∈ pCoreOf 2 I := by
  have : I ⊓ pCoreOf 2 M ≤ pCoreOf 2 I := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 M (hIM hy)⟩
  exact this ⟨hx, hxO⟩

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem theta_inf_mem_Rg (x : L) (hx : (x : G) ∈ conjClosure V H) :
    S.D.θ x ∈ Rg (GaloisField 2 n) := by
  have h1 : S.betaU ⟨x, hx⟩ = S.D.θ x := S.Phi_of_L x
  rw [← h1]
  exact S.betaU_mem_Rg _

theorem exists_inf_of_Rg (hq : ∃ a : GaloisField 2 n, a ≠ 0 ∧ a ^ 2 ≠ 1)
    {r : SL(2, GaloisField 2 n)} (hr : r ∈ Rg (GaloisField 2 n)) :
    ∃ x : L, (x : G) ∈ conjClosure V H ∧ S.D.θ x = r := by
  obtain ⟨r', hr', d, hrd⟩ := Rg_commutator hq hr
  rw [← S.Ubar_eq_Rg] at hr'
  obtain ⟨u₀, hu₀⟩ := hr'
  obtain ⟨a, ha1, haθ⟩ := S.exists_l1 d
  have haH : (a : G) ∈ H :=
    S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have haN : (a : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H haH
  have hu₀N : (u₀ : G) ∈ Subgroup.normalizer (L : Set G) := S.U_le_normL u₀.2
  have hxU : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H := by
    have h1 : (a : G) * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.1 haN _).1 (inv_mem u₀.2)
    have := Subgroup.mul_mem _ u₀.2 h1
    simpa [mul_assoc] using this
  have hxL : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ L := by
    have h1 : (u₀ : G) * a * (u₀ : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hu₀N _).1 a.2
    exact L.mul_mem h1 (L.inv_mem a.2)
  refine ⟨⟨_, hxL⟩, hxU, ?_⟩
  have hu₀' : (u₀ : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u₀.2
  have ha' : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have e : (⟨(u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹,
      (le_sup_left : L ≤ L ⊔ conjClosure V H) hxL⟩ : ↥(L ⊔ conjClosure V H)) =
      ⟨u₀, hu₀'⟩ * ⟨a, ha'⟩ * ⟨u₀, hu₀'⟩⁻¹ * ⟨a, ha'⟩⁻¹ := Subtype.ext (by simp)
  have h1 := S.Phi_of_L ⟨_, hxL⟩
  rw [← h1, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  have h2 : S.Phi ⟨u₀, hu₀'⟩ = r' := hu₀
  have h3 : S.Phi ⟨a, ha'⟩ = dgm d := by rw [S.Phi_of_L a, haθ]
  rw [h2, h3, hrd]

theorem theta_inf_eq_one_of_card_two (hF : Nat.card (GaloisField 2 n) = 2) (x : L)
    (hx : (x : G) ∈ conjClosure V H) : S.D.θ x = 1 := by
  have h1 : S.D.θ x ∈ Rg (GaloisField 2 n) := S.theta_inf_mem_Rg x hx
  have h2 : S.D.θ x ∈ Subgroup.zpowers (c3 (GaloisField 2 n)) := by
    rw [← commutator_eq_zpowers_c3 hF, ← S.D.range_eq]
    exact ⟨x, rfl⟩
  exact zpowers_c3_inf_Rg h2 h1

theorem odd_index_ker_sup :
    ¬ 2 ∣ (S.D.θ.ker ⊔ ((L ⊓ conjClosure V H).subgroupOf L)).index := by
  have key := Subgroup.index_map ((L ⊓ conjClosure V H).subgroupOf L) S.D.θ
  rw [sup_comm S.D.θ.ker ((L ⊓ conjClosure V H).subgroupOf L)]
  rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with hF | hq
  · have hmap : ((L ⊓ conjClosure V H).subgroupOf L).map S.D.θ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot]
      exact S.theta_inf_eq_one_of_card_two hF x (Subgroup.mem_subgroupOf.1 hx).2
    have hrange : S.D.θ.range.index = 2 := by
      rw [S.D.range_eq, commutator_eq_zpowers_c3 hF]
      exact index_zpowers_c3 hF
    rw [hmap, hrange, Subgroup.index_bot, card_SL2_of_card_two hF] at key
    omega
  · have hmap : ((L ⊓ conjClosure V H).subgroupOf L).map S.D.θ = Rg (GaloisField 2 n) := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact S.theta_inf_mem_Rg x (Subgroup.mem_subgroupOf.1 hx).2
      · intro r hr
        obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_Rg hq hr
        exact ⟨x, Subgroup.mem_subgroupOf.2 ⟨x.2, hxU⟩, hx⟩
    obtain ⟨a, ha0, ha1⟩ := hq
    have hrange : S.D.θ.range = ⊤ := by
      rw [S.D.range_eq]
      exact Matrix.SL2.commutator_eq_top ha0 ha1
    rw [hmap, hrange, Subgroup.index_top, mul_one] at key
    rw [← key]
    exact Rg_index_odd

end L2Setting
namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem sx_facts {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    I = L ⊔ U ∧ L ≤ I ∧ U ≤ I ∧ I ≤ L ⊔ T ∧ pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T) ∧
      (∀ x ∈ I, ∀ y ∈ pCoreOf 2 I, x * y * x⁻¹ ∈ pCoreOf 2 I) ∧
      (∀ y ∈ pCoreOf 2 I, ∀ x ∈ U, y * x * y⁻¹ ∈ U) := by
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G23_two hg hgN)
  have hSxO : pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T) := by rw [hI]; exact S.pCoreOf_I_le_O hg hgN
  have hSxT : pCoreOf 2 I ≤ T := hSxO.trans S.O_le_T
  exact ⟨hI', hI' ▸ le_sup_left, hI' ▸ le_sup_right, hI' ▸ S.LU_le_LT, hSxO,
    fun x hx y hy => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 I hx) y).1 hy,
    fun y hy x hx =>
      (Subgroup.mem_normalizer_iff.1 (S.hyp.base.G22_three.2 (hSxT hy)) x).1 hx⟩

theorem L_inf_le_P {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    L ⊓ pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g := by
  obtain ⟨hI', hLI, hUI, hIle, hSxO, hINorm, hSxU⟩ := S.sx_facts hU hg hgN hI
  have hgI : g ∈ I := hLI hg
  have hSxT : pCoreOf 2 I ≤ T := hSxO.trans S.O_le_T
  have hIP := I_le_normalizer_P hI hgI hINorm hSxU
  have hPSx : (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ≤ pCoreOf 2 I :=
    sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)
  set P := (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g with hP
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hLI.trans hIP
  have hBn : ((L ⊓ P).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hLP hl⟩
  have hKker : (L ⊓ pCoreOf 2 I).subgroupOf L = S.D.θ.ker := by
    rw [S.D.ker_eq]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨_, hx⟩
      exact hSxO hx
    · intro hx
      exact ⟨x.2, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI x.2) hx⟩
  have hcent : ∀ k ∈ (L ⊓ pCoreOf 2 I).subgroupOf L, ∀ y : L,
      k * y * k⁻¹ * y⁻¹ ∈ (L ⊓ P).subgroupOf L := by
    intro k hk y
    have hk' := Subgroup.mem_subgroupOf.1 hk
    refine Subgroup.mem_subgroupOf.2 ⟨(k * y * k⁻¹ * y⁻¹ : L).2, ?_⟩
    have h := comm_Sx_mem_P hI hgI hINorm hSxU (hLI y.2) hk'.2
    have := P.inv_mem h
    simpa [mul_assoc] using this
  have key := le_of_central_modulo_two_splitting (Γ := L) (B := (L ⊓ P).subgroupOf L)
    (K := (L ⊓ pCoreOf 2 I).subgroupOf L) (C := (L ⊓ U).subgroupOf L)
    (fun b hb => Subgroup.mem_subgroupOf.2 ⟨b.2, hPSx (Subgroup.mem_subgroupOf.1 hb).2⟩)
    hcent
    ((S.hyp.base.isPGroup_T.to_le (inf_le_right.trans hSxT)).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
    (by
      intro x hx
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
      have h1' := Subgroup.mem_subgroupOf.1 h1
      have h2' := Subgroup.mem_subgroupOf.1 h2
      exact Subgroup.mem_subgroupOf.2
        ⟨x.2, (le_sup_left : U ⊓ pCoreOf 2 I ≤ P) ⟨h2'.2, h1'.2⟩⟩)
    (by rw [hKker, hU]; exact S.odd_index_ker_sup)
    (fun N _ hN => eq_top_of_oTwoUpper_eq S.hyp.base.oTwo_eq N hN)
  intro k hk
  have h1 : (⟨k, hk.1⟩ : L) ∈ (L ⊓ pCoreOf 2 I).subgroupOf L := Subgroup.mem_subgroupOf.2 hk
  exact (Subgroup.mem_subgroupOf.1 (key h1)).2

end L2Setting
namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem exists_inf_mul_mem (hq : ∃ a : GaloisField 2 n, a ≠ 0 ∧ a ^ 2 ≠ 1) {u : G}
    (hu : u ∈ conjClosure V H) :
    ∃ x : L, (x : G) ∈ conjClosure V H ∧ (x : G)⁻¹ * u ∈ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_Rg hq (S.betaU_mem_Rg ⟨u, hu⟩)
  refine ⟨x, hxU, ?_⟩
  have hxLU : (x : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) x.2
  have huLU : u ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have e : (⟨(x : G)⁻¹ * u, Subgroup.mul_mem _ (inv_mem hxLU) huLU⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨x, hxLU⟩⁻¹ * ⟨u, huLU⟩ := Subtype.ext (by simp)
  have h1 : S.Phi ⟨(x : G)⁻¹ * u, Subgroup.mul_mem _ (inv_mem hxLU) huLU⟩ = 1 := by
    rw [e, map_mul, map_inv, S.Phi_of_L x]
    have : S.Phi ⟨u, huLU⟩ = S.betaU ⟨u, hu⟩ := rfl
    rw [this, hx, inv_mul_cancel]
  exact (S.Phi_eq_one_iff _).1 h1

theorem pCoreOf_I_le_P {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g := by
  have hL := S.L_inf_le_P hU hg hgN hI
  obtain ⟨hI', hLI, hUI, hIle, hSxO, -, -⟩ := S.sx_facts hU hg hgN hI
  subst hU
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g with hP
  have hWP : conjClosure V H ⊓ pCoreOf 2 I ≤ P := le_sup_left
  have hmul : ((L ⊔ conjClosure V H : Subgroup G) : Set G) =
      (L : Set G) * (conjClosure V H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ (fun u hu => S.U_le_normL hu)
  intro s hs
  have hsLU : s ∈ L ⊔ conjClosure V H := hI' ▸ pCoreOf_le 2 I hs
  rw [SetLike.mem_coe.symm, hmul] at hsLU
  obtain ⟨l, hl, u, hu, rfl⟩ := hsLU
  rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with hF | hq
  ·
    have hlLU : l ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hl
    have huLU : u ∈ L ⊔ conjClosure V H :=
      (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
    have hsLU : l * u ∈ L ⊔ conjClosure V H := Subgroup.mul_mem _ hlLU huLU
    have h1 : S.Phi ⟨l * u, hsLU⟩ = 1 := (S.Phi_eq_one_iff _).2 (hSxO hs)
    have e : (⟨l * u, hsLU⟩ : ↥(L ⊔ conjClosure V H)) = ⟨l, hlLU⟩ * ⟨u, huLU⟩ := rfl
    rw [e, map_mul, S.Phi_of_L ⟨l, hl⟩] at h1
    have h2 : S.Phi ⟨u, huLU⟩ = S.betaU ⟨u, hu⟩ := rfl
    rw [h2] at h1
    have hRg : S.betaU ⟨u, hu⟩ ∈ Rg (GaloisField 2 n) := S.betaU_mem_Rg _
    have hlθ : S.D.θ ⟨l, hl⟩ = (S.betaU ⟨u, hu⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hz : S.D.θ ⟨l, hl⟩ ∈ Subgroup.zpowers (c3 (GaloisField 2 n)) := by
      rw [← commutator_eq_zpowers_c3 hF, ← S.D.range_eq]
      exact ⟨_, rfl⟩
    have hRg' : S.D.θ ⟨l, hl⟩ ∈ Rg (GaloisField 2 n) := by
      rw [hlθ]
      exact Subgroup.inv_mem _ hRg
    have hθ1 : S.D.θ ⟨l, hl⟩ = 1 := zpowers_c3_inf_Rg hz hRg'
    have hβ1 : S.betaU ⟨u, hu⟩ = 1 := by
      rw [hθ1, one_mul] at h1
      exact h1
    have hlO : l ∈ pCoreOf 2 (L ⊔ T) := by
      have : (⟨l, hl⟩ : L) ∈ S.D.θ.ker := hθ1
      rw [S.D.ker_eq] at this
      exact this
    have huO : u ∈ pCoreOf 2 (L ⊔ T) := (S.betaU_eq_one_iff ⟨u, hu⟩).1 hβ1
    have hlP : l ∈ P := hL ⟨hl, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI hl) hlO⟩
    have huP : u ∈ P := hWP ⟨hu, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hUI hu) huO⟩
    exact P.mul_mem hlP huP
  ·
    obtain ⟨x, hxU, hx⟩ := S.exists_inf_mul_mem hq hu
    have hxI : (x : G) ∈ I := hLI x.2
    have hwI : (x : G)⁻¹ * u ∈ I := Subgroup.mul_mem _ (inv_mem hxI) (hUI hu)
    have hwSx : (x : G)⁻¹ * u ∈ pCoreOf 2 I := mem_pCoreOf_of_mem_pCoreOf_of_le hIle hwI hx
    have hwP : (x : G)⁻¹ * u ∈ P := hWP ⟨Subgroup.mul_mem _ (inv_mem hxU) hu, hwSx⟩
    have hlxSx : l * (x : G) ∈ pCoreOf 2 I := by
      have := Subgroup.mul_mem _ hs (Subgroup.inv_mem _ hwSx)
      simpa [mul_assoc] using this
    have hlxP : l * (x : G) ∈ P := hL ⟨L.mul_mem hl x.2, hlxSx⟩
    have := P.mul_mem hlxP hwP
    simpa [mul_assoc] using this

theorem pCoreOf_I_eq {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    pCoreOf 2 I = (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ∧
      ((pCoreOf 2 I : Subgroup G) : Set G) =
        ((U ⊓ pCoreOf 2 I : Subgroup G) : Set G) * ((rconj (U ⊓ pCoreOf 2 I) g : Subgroup G) : Set G) := by
  obtain ⟨hI', hLI, hUI, hIle, hSxO, hINorm, hSxU⟩ := S.sx_facts hU hg hgN hI
  have hgI : g ∈ I := hLI hg
  have heq : pCoreOf 2 I = (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g :=
    le_antisymm (S.pCoreOf_I_le_P hU hg hgN hI)
      (sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm))
  refine ⟨heq, ?_⟩
  have hnorm := W_le_normalizer_rconj hgI hINorm hUI hSxU
  conv_lhs => rw [heq]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm

end L2Setting

namespace AlmostSpecialL2Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL2Hyp n V V₁ L T H)

include hyp

theorem G23_three {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  subst hS
  subst hW
  exact St.pCoreOf_I_eq hU hg hgN hI

end AlmostSpecialL2Hyp

end CFSG.Quasithin
