module

public import CFSG.Quasithin.H13.L32AL2u

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

section Img

variable {G : Type} [Group G] {H : Subgroup G} {M : Type*} [Group M] (ψ : ↥H →* M)

theorem mem_map_subgroupOf_iff {A : Subgroup G} {x : M} :
    x ∈ (A.subgroupOf H).map ψ ↔ ∃ a : ↥H, (a : G) ∈ A ∧ ψ a = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem map_subgroupOf_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    (A.subgroupOf H).map ψ ≤
      Subgroup.normalizer (((B.subgroupOf H).map ψ : Subgroup M) : Set M) := by
  rintro _ ⟨a, ha, rfl⟩
  have haN := hAB (Subgroup.mem_subgroupOf.mp ha)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨a * b * a⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp haN (b : G)).mp (Subgroup.mem_subgroupOf.mp hb)
    simpa using this
  · rintro ⟨b, hb, hbx⟩
    refine ⟨a⁻¹ * b * a, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) (b : G)).mp
        (Subgroup.mem_subgroupOf.mp hb)
      simpa using this
    · rw [map_mul, map_mul, map_inv, hbx]
      group

theorem exists_pow_of_mem_map {A : Subgroup G} (hA : IsPGroup 2 A) {x : M}
    (hx : x ∈ (A.subgroupOf H).map ψ) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hA ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
  refine ⟨k, ?_⟩
  have h1 : a ^ (2 ^ k) = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  rw [← map_pow, h1, map_one]

end Img

section Congr

variable {W' : Type} [CommGroup W'] {F : Type} [Field F] (e : W' ≃* VM F)

theorem congr_apply_e (f : MulAut W') (x : W') : MulAut.congr e f (e x) = e (f x) := by
  rw [show MulAut.congr e f (e x) = e (f (e.symm (e x))) from rfl, MulEquiv.symm_apply_apply]

theorem commHom_congr_apply (s : MulAut W') (x : W') :
    commHom (MulAut.congr e s) (e x) = e (commHom s x) := by
  rw [commHom_apply, commHom_apply, congr_apply_e, map_mul, map_inv]

theorem card_range_commHom_congr (s : MulAut W') :
    Nat.card (commHom (MulAut.congr e s)).range = Nat.card (commHom s).range := by
  have h : (commHom (MulAut.congr e s)).range = (commHom s).range.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨w, rfl⟩ := e.surjective x
      exact ⟨commHom s w, ⟨w, rfl⟩, (commHom_congr_apply e s w).symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨e w, commHom_congr_apply e s w⟩
  rw [h]
  exact (Nat.card_congr ((commHom s).range.equivMapOfInjective e.toMonoidHom
    e.injective).toEquiv).symm

end Congr

theorem exists_comm_ne_one {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : Nat.card F = 4)
    {t : MulAut (VM F)}
    (hN : t ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))))
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : Nat.card (commHom t).range ≤ 4)
    {D : Subgroup (VM F)} (hD : D.index ≤ 2) : ∃ d ∈ D, commHom t d ≠ 1 := by
  by_contra hall
  push Not at hall
  have hDk : D ≤ (commHom t).ker := fun d hd => MonoidHom.mem_ker.mpr (hall d hd)
  have hk2 : Nat.card (commHom t).range ≤ 2 := by
    rw [← Subgroup.index_ker]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hDk)).trans hD
  rcases inv_cases h4 hN ht2 ht1 with h | ⟨A, rfl⟩
  · omega
  ·
    set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) * matJ with hM
    have hMinv : M * (matJ * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = 1 := by
      rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc matJ, matJ_mul_self, Matrix.one_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]
    let f : F → (commHom (lr A A⁻¹ * trM)).range := fun c =>
      ⟨Multiplicative.ofAdd (c • M), (mem_range_commHom_iff A _).mpr ⟨c, rfl⟩⟩
    have hf : Function.Injective f := fun c c' h => by
      have h1 : c • M = c' • M := Multiplicative.ofAdd.injective (congrArg Subtype.val h)
      have h2 := congrArg (fun X => X * (matJ * ((A⁻¹ : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F))) h1
      simp only [Matrix.smul_mul, hMinv] at h2
      have := congrFun (congrFun h2 0) 0
      simpa using this
    have := Nat.card_le_card_of_injective f hf
    omega

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem mem_img_iff {A : Subgroup G} {f : MulAut (Hat V (A6.g1 T V) W)} :
    f ∈ X.img A ↔ ∃ a : ↥(A6.g1 T V), (a : G) ∈ A ∧ X.top.act a = f :=
  mem_map_subgroupOf_iff _

theorem img_mono {A B : Subgroup G} (h : A ≤ B) : X.img A ≤ X.img B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem act_mem_img {A : Subgroup G} (a : ↥(A6.g1 T V)) (ha : (a : G) ∈ A) :
    X.top.act a ∈ X.img A :=
  ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem relIndex_img (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {R S : Subgroup G} (hRS : R ≤ S)
    (hS : S ≤ A6.g1 T V) (hQR : pCoreOf 2 (A6.g1 T V) ≤ R) :
    (X.img R).relIndex (X.img S) = R.relIndex S := by
  have hker : X.top.act.ker = (pCoreOf 2 (A6.g1 T V)).subgroupOf (A6.g1 T V) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      X.act_eq_one_iff hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334]
  rw [img, img, Subgroup.relIndex_map_map, hker,
    sup_eq_left.mpr (Subgroup.subgroupOf_mono _ hQR),
    sup_eq_left.mpr (Subgroup.subgroupOf_mono _ (hQR.trans hRS)), Subgroup.relIndex_subgroupOf hS]

theorem card_range_le_of_index {t : ↥(A6.g1 T V)} {n : ℕ}
    (hidx : ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf
      (conjClosure V (A6.g1 T V))).index ≤ n) :
    Nat.card (commHom (X.top.act t)).range ≤ n := by
  set U := conjClosure V (A6.g1 T V) with hU
  set s := X.top.act t with hs
  set ρt := Setup.rho U (A6.g1 T V) (le_normalizer_conjClosure V (A6.g1 T V)) t with hρt
  set q := InternalSec.secMk (W.subgroupOf U) with hq
  have hcomm : ∀ u : ↥U, q (commHom ρt u) = commHom s (q u) := by
    intro u
    rw [commHom_apply, commHom_apply, map_mul, map_inv, hs, hq, X.top.act_secMk]
  have hkerU : (commHom ρt).ker = (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf U := by
    ext u
    rw [mem_ker_commHom, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      rw [hρt, Setup.rho_apply_coe] at h1
      calc (u : G) * t = ((t : G) * u * (t : G)⁻¹) * t := by rw [h1]
        _ = t * u := by group
    · intro h
      apply Subtype.ext
      rw [hρt, Setup.rho_apply_coe, ← h]
      group
  have hker : ((commHom ρt).ker).map q ≤ (commHom s).ker := by
    rintro _ ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker, ← hcomm, MonoidHom.mem_ker.mp hu, map_one]
  have h1 : (commHom s).ker.index ≤ (((commHom ρt).ker).map q).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have h2 : (((commHom ρt).ker).map q).index ≤ (commHom ρt).ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
  rw [← Subgroup.index_ker]
  exact h1.trans (h2.trans (by rw [hkerU]; exact hidx))

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
