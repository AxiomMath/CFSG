module

public import CFSG.Quasithin.EmptyFaithful.ModGLatC
public import CFSG.Quasithin.EmptyFaithful.ModGRed1
public import CFSG.Quasithin.EmptyFaithful.ModGSec
public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.S146F1

public section

namespace CFSG.Quasithin.ModG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

section Setup

variable {G : Type} [Group G]

structure Red (K T : Subgroup G) (S D P₁ P₂ E : Subgroup Mg) (ψ : ↥K →* Mg) : Prop where
  lat : M22Lat S D P₁ P₂ E
  sylow : IsSylowTwoOf T (K ⊔ T)
  tn : T ≤ Subgroup.normalizer (K : Set G)
  surj : Function.Surjective ψ
  ker : ψ.ker = (pCoreOf 2 K).subgroupOf K
  imgS : ((T ⊓ K).subgroupOf K).map ψ = S

variable {K T : Subgroup G} {S D P₁ P₂ E : Subgroup Mg} {ψ : ↥K →* Mg}

namespace Red

variable (R : Red K T S D P₁ P₂ E ψ)

include R

theorem sup_le_norm : K ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer R.tn

theorem sup_le_normQ : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
  refine sup_le (le_normalizer_pCoreOf 2 K) ?_
  exact R.tn.trans (normalizer_le_normalizer_pCoreOf 2 K)

theorem Q_le_T [Finite G] : pCoreOf 2 K ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) R.sup_le_normQ
      (pCoreOf_isPGroup 2 K)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf R.sylow)

theorem mem_ker_iff (k : ↥K) : ψ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  have h : k ∈ ψ.ker ↔ k ∈ (pCoreOf 2 K).subgroupOf K := by rw [R.ker]
  exact h

theorem conj_mem {x : G} (hx : x ∈ K ⊔ T) (k : ↥K) : x * (k : G) * x⁻¹ ∈ K := by
  have := (Subgroup.mem_normalizer_iff.1 (R.sup_le_norm hx) (k : G)).1 k.2
  exact this

theorem conj_memQ {x : G} (hx : x ∈ K ⊔ T) {q : G} (hq : q ∈ pCoreOf 2 K) :
    x * q * x⁻¹ ∈ pCoreOf 2 K :=
  (Subgroup.mem_normalizer_iff.1 (R.sup_le_normQ hx) q).1 hq

theorem exists_act {x : G} (hx : x ∈ K ⊔ T) :
    ∃ α : MulAut Mg, ∀ k : ↥K, α (ψ k) = ψ ⟨x * (k : G) * x⁻¹, R.conj_mem hx k⟩ := by
  let φ : MulAut ↥K := K.normalizerMonoidHom ⟨x, R.sup_le_norm hx⟩
  have hφ : ∀ k : ↥K, (φ k : G) = x * (k : G) * x⁻¹ := fun k => rfl
  have hmap : ψ.ker.map φ.toMonoidHom = ψ.ker := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ pCoreOf 2 K := (R.mem_ker_iff k).1 hk
      show φ k ∈ ψ.ker
      rw [MonoidHom.mem_ker, R.mem_ker_iff, hφ]
      exact R.conj_memQ hx hk'
    · intro k hk
      have hk' : (k : G) ∈ pCoreOf 2 K := (R.mem_ker_iff k).1 hk
      refine ⟨φ.symm k, ?_, by simp⟩
      show φ.symm k ∈ ψ.ker
      rw [MonoidHom.mem_ker, R.mem_ker_iff]
      have h1 : (φ.symm k : G) = x⁻¹ * (k : G) * x := by
        have := hφ (φ.symm k)
        rw [MulEquiv.apply_symm_apply] at this
        calc (φ.symm k : G) = x⁻¹ * (x * (φ.symm k : G) * x⁻¹) * x := by group
          _ = x⁻¹ * (k : G) * x := by rw [← this]
      rw [h1]
      have := R.conj_memQ (inv_mem hx) hk'
      simpa using this
  obtain ⟨α, hα⟩ := exists_aut_of_ker ψ R.surj φ hmap
  exact ⟨α, hα⟩

noncomputable def act {x : G} (hx : x ∈ K ⊔ T) : MulAut Mg := Classical.choose (R.exists_act hx)

theorem act_spec {x : G} (hx : x ∈ K ⊔ T) (k : ↥K) :
    R.act hx (ψ k) = ψ ⟨x * (k : G) * x⁻¹, R.conj_mem hx k⟩ :=
  Classical.choose_spec (R.exists_act hx) k

end Red

@[expose] def lft (ψ : ↥K →* Mg) (Z : Subgroup Mg) : Subgroup G := (Z.comap ψ).map K.subtype

theorem mem_lft {Z : Subgroup Mg} {g : G} : g ∈ lft ψ Z ↔ ∃ hg : g ∈ K, ψ ⟨g, hg⟩ ∈ Z := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, by simpa using hk⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem lft_le_K (Z : Subgroup Mg) : lft ψ Z ≤ K := fun _ h => (mem_lft.1 h).1

namespace Red

variable (R : Red K T S D P₁ P₂ E ψ)

include R

theorem Q_le_lft (Z : Subgroup Mg) : pCoreOf 2 K ≤ lft ψ Z := by
  intro q hq
  have hqK : q ∈ K := pCoreOf_le 2 K hq
  refine mem_lft.2 ⟨hqK, ?_⟩
  have : ψ ⟨q, hqK⟩ = 1 := (R.mem_ker_iff ⟨q, hqK⟩).2 hq
  rw [this]
  exact Z.one_mem

theorem conj_lft {x : G} (hx : x ∈ K ⊔ T) {Z : Subgroup Mg} (hZ : Z.map (R.act hx).toMonoidHom ≤ Z)
    {g : G} (hg : g ∈ lft ψ Z) : x * g * x⁻¹ ∈ lft ψ Z := by
  obtain ⟨hgK, hz⟩ := mem_lft.1 hg
  refine mem_lft.2 ⟨R.conj_mem hx ⟨g, hgK⟩, ?_⟩
  have h1 := R.act_spec hx ⟨g, hgK⟩
  rw [← h1]
  exact hZ ⟨_, hz, rfl⟩

theorem normalizes_lft {x : G} (hx : x ∈ K ⊔ T) {Z : Subgroup Mg}
    (hZ : Z.map (R.act hx).toMonoidHom = Z) : x ∈ Subgroup.normalizer (lft ψ Z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => R.conj_lft hx hZ.le hg
  · intro hg
    obtain ⟨hgK', hz⟩ := mem_lft.1 hg
    have hgK : g ∈ K := by
      have := R.conj_mem (inv_mem hx) ⟨x * g * x⁻¹, hgK'⟩
      simpa [mul_assoc] using this
    refine mem_lft.2 ⟨hgK, ?_⟩
    have h1 := R.act_spec hx ⟨g, hgK⟩
    have h2 : (R.act hx) (ψ ⟨g, hgK⟩) ∈ Z := by rw [h1]; exact hz
    rw [← hZ] at h2
    obtain ⟨z, hz', hzz⟩ := h2
    have : z = ψ ⟨g, hgK⟩ := (R.act hx).injective hzz
    rw [← this]
    exact hz'

theorem act_S {t : G} (ht : t ∈ T) : S.map (R.act (Subgroup.mem_sup_right ht)).toMonoidHom = S := by
  have hS : ∀ y, y ∈ S ↔ y ∈ ((T ⊓ K).subgroupOf K).map ψ := fun y => by rw [R.imgS]
  apply map_eq_of_le_aut
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨k, hk, rfl⟩ := (hS s).1 hs
  have hkT : (k : G) ∈ T ⊓ K := hk
  show (R.act (Subgroup.mem_sup_right ht)) (ψ k) ∈ S
  rw [R.act_spec]
  refine (hS _).2 ⟨⟨t * (k : G) * t⁻¹, R.conj_mem (Subgroup.mem_sup_right ht) k⟩, ?_, rfl⟩
  show t * (k : G) * t⁻¹ ∈ T ⊓ K
  exact ⟨T.mul_mem (T.mul_mem ht hkT.1) (T.inv_mem ht), R.conj_mem (Subgroup.mem_sup_right ht) k⟩

theorem T_normalizes_lft {P : Subgroup Mg}
    (hP : ∀ α : MulAut Mg, S.map α.toMonoidHom = S → P.map α.toMonoidHom = P) :
    T ≤ Subgroup.normalizer (lft ψ P : Set G) := by
  intro t ht
  exact R.normalizes_lft (Subgroup.mem_sup_right ht) (hP _ (R.act_S ht))

end Red

theorem isSolvable_map {K' M' : Type*} [Group K'] [Group M'] (H : Subgroup K') [Group.IsSolvable ↥H]
    (f : K' →* M') : Group.IsSolvable ↥(H.map f) :=
  Group.isSolvable_of_surjective (f := f.subgroupMap H) (f.subgroupMap_surjective H)

namespace Red

variable (R : Red K T S D P₁ P₂ E ψ)

include R

theorem normalizes_of_solvable {Y : Subgroup G} (hTY : T ≤ Y) (hYX : Y ≤ K ⊔ T)
    (hY : Group.IsSolvable ↥Y) : Y ≤ Subgroup.normalizer (lft ψ D : Set G) := by
  intro x hxY
  have hxX : x ∈ K ⊔ T := hYX hxY
  set α : MulAut Mg := R.act hxX with hα
  set Z : Subgroup Mg := ((Y ⊓ K).subgroupOf K).map ψ with hZ
  have hSZ : S ≤ Z := by
    have hS : ∀ y, y ∈ S ↔ y ∈ ((T ⊓ K).subgroupOf K).map ψ := fun y => by rw [R.imgS]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hS y).1 hy
    exact ⟨k, ⟨hTY hk.1, hk.2⟩, rfl⟩
  have hsolv1 : Group.IsSolvable ↥(Y ⊓ K) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (inf_le_left : Y ⊓ K ≤ Y))
  have hsolv2 : Group.IsSolvable ↥((Y ⊓ K).subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ K ≤ K)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ K ≤ K)).injective
  have hZsolv : Group.IsSolvable ↥Z := isSolvable_map _ ψ
  have hZD : Z ≤ D := R.lat.lat Z hSZ hZsolv
  have hαZ : Z.map α.toMonoidHom = Z := by
    apply map_eq_of_le_aut
    rintro _ ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    show α (ψ k) ∈ Z
    rw [hα, R.act_spec hxX k]
    refine ⟨⟨x * (k : G) * x⁻¹, R.conj_mem hxX k⟩, ?_, rfl⟩
    show x * (k : G) * x⁻¹ ∈ Y ⊓ K
    exact ⟨Y.mul_mem (Y.mul_mem hxY hk.1) (Y.inv_mem hxY), R.conj_mem hxX k⟩
  obtain ⟨z, hzZ, hz⟩ := exists_conj_fixing R.lat.sylow.1 R.lat.sylow.2 hSZ α hαZ
  have hD1 := (R.lat.inv (MulAut.conj z * α) hz).1
  have hDα : D.map α.toMonoidHom = D := by
    have hzD : z ∈ D := hZD hzZ
    have h2 : D.map (MulAut.conj z⁻¹ * (MulAut.conj z * α)).toMonoidHom = D := by
      have : D.map (MulAut.conj z⁻¹ * (MulAut.conj z * α)).toMonoidHom =
          (D.map (MulAut.conj z * α).toMonoidHom).map (MulAut.conj z⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [this, hD1]
      exact map_conj_of_mem (D.inv_mem hzD)
    have h3 : MulAut.conj z⁻¹ * (MulAut.conj z * α) = α := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [h3] at h2
    exact h2
  exact R.normalizes_lft hxX hDα

omit R in
theorem exists_mul_of_mem_sup' {H L : Subgroup G} (h : L ≤ Subgroup.normalizer (H : Set G)) {y : G}
    (hy : y ∈ H ⊔ L) : ∃ p ∈ H, ∃ t ∈ L, y = p * t := by
  let W : Subgroup G :=
    { carrier := {y | ∃ p ∈ H, ∃ t ∈ L, y = p * t}
      one_mem' := ⟨1, H.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, t, ht, rfl⟩ ⟨p', hp', t', ht', rfl⟩
        refine ⟨p * (t * p' * t⁻¹), H.mul_mem hp ((Subgroup.mem_normalizer_iff.1 (h ht) p').1 hp'),
          t * t', L.mul_mem ht ht', by group⟩
      inv_mem' := by
        rintro _ ⟨p, hp, t, ht, rfl⟩
        refine ⟨t⁻¹ * p⁻¹ * t, ?_, t⁻¹, L.inv_mem ht, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (h (L.inv_mem ht)) p⁻¹).1 (H.inv_mem hp)
        simpa using this }
  have hH : H ≤ W := fun p hp => ⟨p, hp, 1, L.one_mem, by simp⟩
  have hL : L ≤ W := fun t ht => ⟨1, H.one_mem, t, ht, by simp⟩
  exact (sup_le hH hL) hy

theorem solvable_sup [Finite G] {P : Subgroup Mg} (reps : Fin 3 → Mg) (hreps : ∀ i, reps i ∈ P)
    (hcov : ∀ p ∈ P, ∃ i, (reps i)⁻¹ * p ∈ S) (hTP : T ≤ Subgroup.normalizer (lft ψ P : Set G)) :
    Group.IsSolvable ↥(lft ψ P ⊔ T) := by
  classical
  set Y : Subgroup G := lft ψ P ⊔ T with hY
  have hTY : T ≤ Y := le_sup_right
  have hT2 : IsPGroup 2 ↥(T.subgroupOf Y) :=
    R.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hS : ∀ y, y ∈ S ↔ y ∈ ((T ⊓ K).subgroupOf K).map ψ := fun y => by rw [R.imgS]
  have hlift : ∀ i, ∃ k : ↥K, ψ k = reps i := fun i => R.surj (reps i)
  choose kk hkk using hlift
  have hkkP : ∀ i, (kk i : G) ∈ lft ψ P := fun i =>
    mem_lft.2 ⟨(kk i).2, by simpa [hkk i] using hreps i⟩
  let reps' : Fin 3 → ↥Y := fun i => ⟨(kk i : G), Subgroup.mem_sup_left (hkkP i)⟩
  refine isSolvable_of_cosets (T.subgroupOf Y) hT2 3 le_rfl reps' ?_
  intro y
  obtain ⟨p, hp, t, ht, hyp⟩ := exists_mul_of_mem_sup' hTP y.2
  obtain ⟨hpK, hpP⟩ := mem_lft.1 hp
  obtain ⟨i, hi⟩ := hcov _ hpP
  obtain ⟨u, hu, hψu⟩ := (hS _).1 hi
  refine ⟨i, ?_⟩
  set a : ↥K := (kk i)⁻¹ * ⟨p, hpK⟩ with ha
  have hψa : ψ a = ψ u := by
    rw [ha, map_mul, map_inv, hkk i]
    exact hψu.symm
  have hker : a * u⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψa, mul_inv_cancel]
  have hQ : ((a * u⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
    rw [← R.mem_ker_iff]
    exact hker
  have haT : (a : G) ∈ T := by
    have h1 : (a : G) = ((a * u⁻¹ : ↥K) : G) * (u : G) := by
      simp
    rw [h1]
    exact T.mul_mem (R.Q_le_T hQ) hu.1
  show ((reps' i)⁻¹ * y : ↥Y) ∈ T.subgroupOf Y
  rw [Subgroup.mem_subgroupOf]
  have h2 : (((reps' i)⁻¹ * y : ↥Y) : G) = (a : G) * t := by
    have : ((reps' i)⁻¹ * y : ↥Y) = ⟨((kk i : G))⁻¹ * (p * t), by
      exact Y.mul_mem (Y.inv_mem (Subgroup.mem_sup_left (hkkP i))) (hyp ▸ y.2)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, reps']
      rw [hyp]
    rw [this]
    simp [ha, mul_assoc]
  rw [h2]
  exact T.mul_mem haT ht

theorem lft_le_solvGen_of [Finite G] {P : Subgroup Mg} (reps : Fin 3 → Mg) (hreps : ∀ i, reps i ∈ P)
    (hcov : ∀ p ∈ P, ∃ i, (reps i)⁻¹ * p ∈ S)
    (hP : ∀ α : MulAut Mg, S.map α.toMonoidHom = S → P.map α.toMonoidHom = P) :
    lft ψ P ≤ solvGen T (K ⊔ T) := by
  have hTP := R.T_normalizes_lft hP
  have hsolv := R.solvable_sup reps hreps hcov hTP
  have hle : lft ψ P ⊔ T ≤ solvGen T (K ⊔ T) :=
    le_solvGen le_sup_right (sup_le ((lft_le_K P).trans le_sup_left) le_sup_right) hsolv
  exact le_sup_left.trans hle

theorem D_le_image [Finite G] : D ≤ ((solvGen T (K ⊔ T) ⊓ K).subgroupOf K).map ψ := by
  obtain ⟨reps₁, hreps₁, hcov₁⟩ := R.lat.cos₁
  obtain ⟨reps₂, hreps₂, hcov₂⟩ := R.lat.cos₂
  have h1 := R.lft_le_solvGen_of reps₁ hreps₁ hcov₁ (fun α h => (R.lat.inv α h).2.1)
  have h2 := R.lft_le_solvGen_of reps₂ hreps₂ hcov₂ (fun α h => (R.lat.inv α h).2.2)
  set J := solvGen T (K ⊔ T) with hJ
  set J' : Subgroup Mg := ((J ⊓ K).subgroupOf K).map ψ with hJ'
  have hP : ∀ (P : Subgroup Mg), lft ψ P ≤ J → P ≤ J' := by
    intro P hPJ p hp
    obtain ⟨k, rfl⟩ := R.surj p
    have hk : (k : G) ∈ lft ψ P := mem_lft.2 ⟨k.2, by simpa using hp⟩
    exact ⟨k, ⟨hPJ hk, k.2⟩, rfl⟩
  exact R.lat.gen.trans (sup_le (hP _ h1) (hP _ h2))

theorem solvGen_le_normalizer : solvGen T (K ⊔ T) ≤ Subgroup.normalizer (lft ψ D : Set G) :=
  solvGen_le fun _ hTY hYX hY => R.normalizes_of_solvable hTY hYX hY

theorem oTwoUpper_X_le [Finite G] : oTwoUpper (K ⊔ T) ≤ K := by
  refine Der6A.oTwoUpper_le_of_normal_sup le_sup_left ?_ R.sylow.2.1 le_sup_right le_rfl
  rw [Subgroup.normal_subgroupOf_iff le_sup_left]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.1 (R.sup_le_norm hk) h).1 hh

theorem oTwoUpper_le_lft [Finite G] : oTwoUpper (solvGen T (K ⊔ T)) ≤ lft ψ D := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxJ, hxodd⟩
  have hxX : x ∈ K ⊔ T := solvGen_le_right hxJ
  have hxK : x ∈ K :=
    R.oTwoUpper_X_le (oTwoUpper_mono solvGen_le_right (mem_oTwoUpper_of_odd hxJ hxodd))
  have hxN := R.solvGen_le_normalizer hxJ
  have hn : ψ ⟨x, hxK⟩ ∈ Subgroup.normalizer (D : Set Mg) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    obtain ⟨k, rfl⟩ := R.surj d
    have hconj : ψ ⟨x, hxK⟩ * ψ k * (ψ ⟨x, hxK⟩)⁻¹ = ψ ⟨x * (k : G) * x⁻¹, R.conj_mem hxX k⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj]
    have h1 : ψ k ∈ D ↔ (k : G) ∈ lft ψ D := by
      constructor
      · intro h
        exact mem_lft.2 ⟨k.2, h⟩
      · intro h
        exact (mem_lft.1 h).2
    have h2 : ψ ⟨x * (k : G) * x⁻¹, R.conj_mem hxX k⟩ ∈ D ↔ x * (k : G) * x⁻¹ ∈ lft ψ D := by
      constructor
      · intro h
        exact mem_lft.2 ⟨R.conj_mem hxX k, h⟩
      · intro h
        exact (mem_lft.1 h).2
    rw [h1, h2]
    exact Subgroup.mem_normalizer_iff.1 hxN (k : G)
  exact mem_lft.2 ⟨hxK, R.lat.selfnorm _ hn⟩

theorem lft_D_le_A [Finite G] :
    lft ψ D ≤ oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K := by
  set J := solvGen T (K ⊔ T) with hJ
  set A := oTwoUpper J ⊔ pCoreOf 2 K with hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ k ∈ ψ.ker, ∃ b : ℕ, k ^ 2 ^ b = 1 := by
    intro k hk
    have hk' : (k : G) ∈ pCoreOf 2 K := (R.mem_ker_iff k).1 hk
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 K) ⟨(k : G), hk'⟩
    refine ⟨b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simpa using this
  set Ā : Subgroup Mg := ((A ⊓ K).subgroupOf K).map ψ with hĀ
  have hodd : ∀ d : Mg, d ∈ D → Odd (orderOf d) → d ∈ Ā := by
    intro d hd hdodd
    obtain ⟨x, hxW, hxodd, hxd⟩ := exists_odd_lift ψ hker ((J ⊓ K).subgroupOf K) (R.D_le_image hd) hdodd
    have hxJ : (x : G) ∈ J := hxW.1
    have hodd' : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
    have hxA : (x : G) ∈ A := Subgroup.mem_sup_left (mem_oTwoUpper_of_odd hxJ hodd')
    exact ⟨x, ⟨hxA, x.2⟩, hxd⟩
  have hDĀ : D ≤ Ā := by
    refine R.lat.odd.trans ?_
    rw [Subgroup.closure_le]
    rintro d ⟨hd, hdodd⟩
    exact hodd d hd hdodd
  intro g hg
  obtain ⟨hgK, hgD⟩ := mem_lft.1 hg
  obtain ⟨a, ha, hag⟩ := hDĀ hgD
  have hker' : (⟨g, hgK⟩ : ↥K) * a⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hag, mul_inv_cancel]
  have hQ : (((⟨g, hgK⟩ : ↥K) * a⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
    rw [← R.mem_ker_iff]
    exact hker'
  have h3 : g = (((⟨g, hgK⟩ : ↥K) * a⁻¹ : ↥K) : G) * (a : G) := by simp
  rw [h3]
  exact A.mul_mem (Subgroup.mem_sup_right hQ) ha.1

theorem secExt [Finite G] :
    SecExt (oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K) (pCoreOf 2 K) (IsE2 4) (IsAlt 6) := by
  have hA : oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K = lft ψ D :=
    le_antisymm (sup_le R.oTwoUpper_le_lft (R.Q_le_lft D)) R.lft_D_le_A
  rw [hA]
  let χ : ↥(lft ψ D) →* Mg := ψ.comp (Subgroup.inclusion (lft_le_K D))
  refine secExt_of_hom (lft ψ D) (pCoreOf 2 K) D E χ ?_ ?_ R.lat.alt
  · ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ψ ⟨(a : G), lft_le_K D a.2⟩ = 1 ↔ (a : G) ∈ pCoreOf 2 K
    exact R.mem_ker_iff _
  · ext d
    constructor
    · rintro ⟨a, rfl⟩
      exact (mem_lft.1 a.2).2
    · intro hd
      obtain ⟨k, rfl⟩ := R.surj d
      exact ⟨⟨(k : G), mem_lft.2 ⟨k.2, hd⟩⟩, rfl⟩

end Red

end Setup

end CFSG.Quasithin.ModG
