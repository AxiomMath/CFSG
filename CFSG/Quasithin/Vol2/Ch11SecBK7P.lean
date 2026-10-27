module

public import CFSG.Quasithin.Vol2.Ch11SecBK7O
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecBK7E
public import CFSG.Quasithin.Vol2.Ch11SecBK7K

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative

namespace K7

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem index_eq_card_of_iff (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {N : Subgroup W} {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hN : ∀ w, w ∈ N ↔ Matrix.toBilin' (spJ K) (f w) y = 0) : N.index = Nat.card K := by
  let φ : W →* Multiplicative K :=
    { toFun := fun v => Multiplicative.ofAdd (Matrix.toBilin' (spJ K) (f v) y)
      map_one' := by rw [hf.map_one, map_zero, LinearMap.zero_apply, ofAdd_zero]
      map_mul' := fun a b => by rw [hf.map_mul, bil_add_left, ofAdd_add] }
  have hker : φ.ker = N := by
    ext v
    rw [MonoidHom.mem_ker, hN]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨x, hx⟩ := exists_bil_eq_one hy
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd c • x)
    refine ⟨w, ?_⟩
    change Multiplicative.ofAdd (Matrix.toBilin' (spJ K) (f w) y) = c
    rw [hw, bil_smul_left, hx, mul_one, ofAdd_toAdd]
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  rfl

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G} {n : ℕ}

theorem not_le_centralizer_sp4 (hn : 2 ≤ n) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hnat : NatModuleOf L V n) (hk : KindSp4 L V n)
    (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ¬ V ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  intro hle
  obtain ⟨_, K, _, _, _, hK, π, f, hf, g, hg⟩ := exists_coord_sp4 hn hLV hnat hk hTS hTL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut ↥V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hZfix := fix_of_autOn (L := L) (V := V)
  set y := mat 2 K g *ᵥ vec4 1 0 0 0 with hydef
  have hy : y ≠ 0 := v0_ne_zero g
  have h2q : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hT2 : IsPGroup 2 T := hTS.2.1
  set k : ↥T → MulAut ↥V := fun t => SecA.conjV V t (hTV t.2) with hkdef
  have hk1 : k 1 = 1 := conjV_one V _
  have hkmul : ∀ a b : ↥T, k (a * b) = k a * k b := fun a b => SecA.conjV_mul V _ _
  have hkinv : ∀ t : ↥T, (k t)⁻¹ = SecA.conjV V (t : G)⁻¹ (Subgroup.inv_mem _ (hTV t.2)) :=
    fun t => (SecA.conjV_inv V (hTV t.2)).symm
  have hkZ : ∀ (t : ↥T) (z : ↥V), z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V →
      k t z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := fun t z hz =>
    G2Q8.conjV_mem_centralizer (hTL t.2) (hTV t.2) hz
  have hkH : ∀ (t : ↥T), ∀ h ∈ autOn L V, k t * h * (k t)⁻¹ ∈ autOn L V := fun t h hh =>
    G2Q8.conjV_mul_conjV_inv_mem (hTL t.2) (hTV t.2) hh
  have hkS : ∀ (t : ↥T), ∀ s ∈ autOn (T ⊓ L) V, (k t)⁻¹ * s * k t ∈ autOn (T ⊓ L) V := by
    intro t s hs
    obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    have hmem : (t : G)⁻¹ * x * t ∈ T ⊓ L := by
      refine ⟨T.mul_mem (T.mul_mem (T.inv_mem t.2) hx.1) t.2, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTL t.2)) x).mp hx.2
      rwa [inv_inv] at this
    have e : (k t)⁻¹ * SecA.conjV V x hxV * k t = SecA.conjV V ((t : G)⁻¹ * x * t)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTV t.2)) hxV)
          (hTV t.2)) := by
      rw [hkinv]
      show SecA.conjV V _ _ * SecA.conjV V x hxV * SecA.conjV V (t : G) (hTV t.2) = _
      rw [← SecA.conjV_mul, ← SecA.conjV_mul]
    rw [e]
    exact SecA.conjV_mem_autOn hmem _
  have hP : ∀ (t : ↥T) (w : ↥V), (∃ c : K, f w = c • y) → ∃ c : K, f (k t w) = c • y := by
    intro t w hw
    rw [← mem_gS1_iff, ← fixedW_iff_sp hf hg] at hw ⊢
    intro s hs
    have e : s (k t w) * (k t w)⁻¹ = k t (((k t)⁻¹ * s * k t) w * w⁻¹) := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [e]
    exact hkZ t _ (hw _ (hkS t s hs))
  have hnorm : ∀ (t : ↥T) (c : K), ∃ c' : K,
      k t * ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) * (k t)⁻¹ =
        ((π (trv y c') : ↥(autOn L V)) : MulAut ↥V) := by
    intro t c
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K), π γ = ⟨_, hkH t _ (π (trv y c)).2⟩ := hf.onto _
    have hγ' : ((π γ : ↥(autOn L V)) : MulAut ↥V) =
        k t * ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) * (k t)⁻¹ := by rw [hγ]
    obtain ⟨c', hc'⟩ := eq_trv_of_range hy (γ := γ) fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      have e : ((π γ : ↥(autOn L V)) : MulAut ↥V) w * w⁻¹ =
          k t (((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) ((k t)⁻¹ w) * ((k t)⁻¹ w)⁻¹) := by
        rw [hγ', map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      obtain ⟨d, hd⟩ := hP t _ ⟨_, f_gen hf y c ((k t)⁻¹ w)⟩
      refine ⟨d, ?_⟩
      rw [← hf.act4, ← hf.map_mul_inv, e, hd]
    exact ⟨c', by rw [← hγ', hc']⟩
  set S : Set (MulAut ↥V) := Set.range fun c : K => ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V)
    with hSdef
  have hinj : Function.Injective fun c : K => ((π (trv y c) : ↥(autOn L V)) : MulAut ↥V) :=
    fun c c' h => trv_injective hf hy h
  have hScard : Nat.card S = Nat.card K := Nat.card_range_of_injective hinj
  have h1S : (1 : MulAut ↥V) ∈ S := ⟨0, by
    show ((π (trv y 0) : ↥(autOn L V)) : MulAut ↥V) = 1
    rw [trv_zero, map_one, Subgroup.coe_one]⟩
  obtain ⟨x₀, ⟨c₀, rfl⟩, hx₀1, hx₀⟩ := exists_fixed_ne hT2 (fun t x => k t * x * (k t)⁻¹)
    (fun x => by simp only [hk1, one_mul, inv_one, mul_one])
    (fun a b x => by simp only [hkmul, _root_.mul_inv_rev, mul_assoc])
    (S := S) (by
      rintro t _ ⟨c, rfl⟩
      obtain ⟨c', hc'⟩ := hnorm t c
      exact ⟨c', hc'.symm⟩) (hScard ▸ h2q) h1S
    (fun t => by simp only [mul_one, mul_inv_cancel])
  beta_reduce at hx₀ hx₀1
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hx₀1
    rw [trv_zero, map_one, Subgroup.coe_one]
  set x₀ := ((π (trv y c₀) : ↥(autOn L V)) : MulAut ↥V) with hx₀def
  have hcomm : ∀ (t : ↥T) (v : ↥V), k t (x₀ v) = x₀ (k t v) := fun t v => by
    have := congrArg (fun φ : MulAut ↥V => φ (k t v)) (hx₀ t)
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using this
  let δ : ↥V →* ↥V :=
    { toFun := fun v => x₀ v * v⁻¹
      map_one' := by rw [map_one, one_mul, inv_one]
      map_mul' := fun a b => by
        rw [map_mul, _root_.mul_inv_rev]
        rw [mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm] }
  have hδker : ∀ v, v ∈ δ.ker ↔ Matrix.toBilin' (spJ K) (f v) y = 0 := by
    intro v
    rw [MonoidHom.mem_ker]
    change x₀ v * v⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    exact ⟨bil_eq_zero_of_trv_fix hf hy hc₀, trv_fix hf hZfix hy c₀⟩
  have hDcard : Nat.card (δ.range : Set ↥V) = Nat.card K := by
    rw [← index_eq_card_of_iff hf hy hδker, Subgroup.index_ker]
    rfl
  obtain ⟨a, ⟨v₀, rfl⟩, ha1, ha⟩ := exists_fixed_ne hT2 (fun t v => k t v)
    (fun v => by rw [hk1, MulAut.one_apply]) (fun a b v => by rw [hkmul, MulAut.mul_apply])
    (S := (δ.range : Set ↥V)) (by
      rintro t _ ⟨v, rfl⟩
      refine ⟨k t v, ?_⟩
      change x₀ (k t v) * (k t v)⁻¹ = k t (x₀ v * v⁻¹)
      rw [map_mul, map_inv, hcomm]) (hDcard ▸ h2q) (one_mem δ.range) (fun t => map_one _)
  have haT : ((δ v₀ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    refine ⟨(δ v₀).2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have h1 := congrArg Subtype.val (ha ⟨t, ht⟩)
    rw [hkdef, SecA.conjV_apply_coe] at h1
    calc t * ((δ v₀ : ↥V) : G) = t * ((δ v₀ : ↥V) : G) * t⁻¹ * t := by group
      _ = _ := by rw [h1]
  have haL := hle haT
  have haZ : δ v₀ ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V := haL
  apply ha1
  have hf0 : f (δ v₀) = 0 := (hf.ker _).mpr haZ
  change f (x₀ v₀ * v₀⁻¹) = 0 at hf0
  rw [f_gen hf, smul_eq_zero] at hf0
  have hb : Matrix.toBilin' (spJ K) (f v₀) y = 0 :=
    (mul_eq_zero.mp (hf0.resolve_right hy)).resolve_left hc₀
  exact (hδker v₀).mpr hb

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
