module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

namespace Sp4Z

theorem conj_mem_centralizer {A : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (hz : z ∈ Subgroup.centralizer (A : Set G)) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro u hu
  have hu' : g⁻¹ * u * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
    rwa [inv_inv] at this
  have h := hz _ hu'
  calc u * (g * z * g⁻¹) = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * u := by group

theorem mem_normalizer_centralizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_centralizer hg hz, fun hz => ?_⟩
  have := conj_mem_centralizer (Subgroup.inv_mem _ hg) hz
  convert this using 1
  group

theorem mem_normalizer_blockZ [Finite G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (blockZ K : Set G) :=
  mem_normalizer_inf (mem_normalizer_commutator ((normalizer_le_normalizer_pCoreOf 2 K) hg) hg)
    (mem_normalizer_centralizer hg)

theorem le_normalizer_map_conj [Finite G] {S A : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) (hSA : S ≤ Subgroup.normalizer (A : Set G)) :
    S ≤ Subgroup.normalizer ((A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro s hs
  apply mem_normalizer_of_map_conj_le
  have hs' : t⁻¹ * s * t ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) s).mp hs
    rwa [inv_inv] at this
  have e : s * t = t * (t⁻¹ * s * t) := by group
  rw [← map_conj_mul, e, map_conj_mul, map_conj_eq_of_mem_normalizer (hSA hs')]

theorem le_centralizer_of_inf_eq_bot {U₁ Z₁ Z₂ L : Subgroup G}
    (hU₁ : ∀ z ∈ Z₂, z ∈ Subgroup.normalizer (U₁ : Set G))
    (hZ₂ : ∀ u ∈ U₁, u ∈ Subgroup.normalizer (Z₂ : Set G))
    (hLZ₂ : L ≤ Subgroup.centralizer (Z₂ : Set G))
    (hCL : ∀ u ∈ U₁, (∀ l ∈ L, l * u = u * l) → u ∈ Z₁) (hZZ : Z₁ ⊓ Z₂ = ⊥) :
    Z₂ ≤ Subgroup.centralizer (U₁ : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hc1 : u * z * u⁻¹ * z⁻¹ ∈ U₁ := by
    have h1 : z * u⁻¹ * z⁻¹ ∈ U₁ :=
      (Subgroup.mem_normalizer_iff.mp (hU₁ z hz) _).mp (U₁.inv_mem hu)
    have e : u * z * u⁻¹ * z⁻¹ = u * (z * u⁻¹ * z⁻¹) := by group
    rw [e]
    exact U₁.mul_mem hu h1
  have hc2 : u * z * u⁻¹ * z⁻¹ ∈ Z₂ :=
    Z₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZ₂ u hu) z).mp hz) (Z₂.inv_mem hz)
  have hc3 : u * z * u⁻¹ * z⁻¹ ∈ Z₁ := hCL _ hc1 fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hLZ₂ hl) _ hc2).symm
  have hc4 : u * z * u⁻¹ * z⁻¹ = 1 := by
    have h : u * z * u⁻¹ * z⁻¹ ∈ Z₁ ⊓ Z₂ := ⟨hc3, hc2⟩
    rw [hZZ] at h
    exact Subgroup.mem_bot.mp h
  calc u * z = (u * z * u⁻¹ * z⁻¹) * (z * u) := by group
    _ = z * u := by rw [hc4, one_mul]

section Blocks

variable {K : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Hm : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥K →* ↥Hm}
  {β : ↥(blockU K) →* Multiplicative (ι → F)}

theorem mem_pCoreOf_of_mem_centralizer (hb : IsMatrixBlockTypeWith K Hm α β) (k : ↥K)
    (hk : (k : G) ∈ Subgroup.centralizer (blockU K : Set G)) : (k : G) ∈ pCoreOf 2 K := by
  obtain ⟨-, hker, hβ, -, hequiv⟩ := hb
  have hfix : ∀ v : ι → F,
      ((α k : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *ᵥ v = v := by
    intro v
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
    have hcomm : (u : G) = k * u * (k : G)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp hk u u.2, mul_inv_cancel_right]
    have h1 := hequiv k u u hcomm
    rw [hu, toAdd_ofAdd] at h1
    exact h1.symm
  have h1 : α k = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    have h := congrFun (hfix (Pi.single j 1)) i
    simpa [mulVec, dotProduct, Pi.single_apply, one_apply, eq_comm] using h
  have h2 : k ∈ α.ker := MonoidHom.mem_ker.mpr h1
  rw [hker] at h2
  exact (mem_pCoreOf_iff' k).mpr h2

theorem commutator_mem_pCoreOf (hb : IsMatrixBlockTypeWith K Hm α β) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxU : x ∈ Subgroup.centralizer (blockU K : Set G)) {k : G} (hk : k ∈ K) :
    ⁅x, k⁆ ∈ pCoreOf 2 K := by
  have hKU : K ≤ Subgroup.normalizer ((blockU K) : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 K) K
  have hcK : ⁅x, k⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk) (K.inv_mem hk)
  have hcU : ⁅x, k⁆ ∈ Subgroup.centralizer (blockU K : Set G) := by
    rw [commutatorElement_def, show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
    exact Subgroup.mul_mem _ hxU (conj_mem_centralizer (hKU hk) (Subgroup.inv_mem _ hxU))
  exact mem_pCoreOf_of_mem_centralizer hb ⟨_, hcK⟩ hcU

end Blocks

end Sp4Z

namespace Setting432K

variable [Finite G] {T M L I H K : Subgroup G} {n : ℕ} {t : G}
  (sk : Setting432K G T M L n I H K t)
include sk

theorem le_centralizer_blockZ : L ≤ Subgroup.centralizer (blockZ K : Set G) := fun l hl =>
  Subgroup.mem_centralizer_iff.mpr fun _ hz =>
    ((Subgroup.mem_centralizer_iff.mp hz.2) l (sk.L_le_K hl)).symm

theorem le_centralizer_map_conj_blockZ :
    L ≤ Subgroup.centralizer
      (((blockZ K).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    sk.base.hyp.normal (sk.base.hyp.T_le sk.t_mem)
  have hl' : t⁻¹ * l * t ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) l).mp hl
    rwa [inv_inv] at this
  have h := (Subgroup.mem_centralizer_iff.mp (sk.le_centralizer_blockZ hl')) z hz
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * z * t⁻¹ * l = t * (z * (t⁻¹ * l * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * l * t) * z) * t⁻¹ := by rw [h]
    _ = l * (t * z * t⁻¹) := by group

theorem blockZ_inf_map_conj_eq_bot :
    blockZ K ⊓ (blockZ K).map (MulAut.conj t).toMonoidHom = ⊥ := by
  obtain ⟨Zt, hZt⟩ : ∃ Zt : Subgroup G, Zt = (blockZ K).map (MulAut.conj t).toMonoidHom :=
    ⟨_, rfl⟩
  rw [← hZt]
  by_contra hne
  have hSK := sk.S_le_normalizer
  have hSZ : T ⊓ H ≤ Subgroup.normalizer (blockZ K : Set G) := fun s hs =>
    Sp4Z.mem_normalizer_blockZ (hSK hs)
  have hSZt : T ⊓ H ≤ Subgroup.normalizer (Zt : Set G) := by
    rw [hZt]
    exact Sp4Z.le_normalizer_map_conj sk.t_normalizer hSZ
  have hLZt : L ≤ Subgroup.centralizer (Zt : Set G) := by
    rw [hZt]
    exact sk.le_centralizer_map_conj_blockZ
  have htX : t ∈ Subgroup.normalizer ((blockZ K ⊓ Zt : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_le
    refine (Subgroup.map_inf_le _ _ _).trans ?_
    rw [hZt, ← map_conj_mul, ← pow_two, map_conj_eq_of_mem_normalizer (hSZ sk.t_sq), inf_comm]
  have hX : L ⊔ (T ⊓ H ⊔ Subgroup.zpowers t) ≤
      Subgroup.normalizer ((blockZ K ⊓ Zt : Subgroup G) : Set G) :=
    _root_.sup_le
      (fun l hl => mem_normalizer_inf
        (Subgroup.centralizer_le_normalizer _ (sk.le_centralizer_blockZ hl))
        (Subgroup.centralizer_le_normalizer _ (hLZt hl)))
      (_root_.sup_le (fun s hs => mem_normalizer_inf (hSZ hs) (hSZt hs))
        (Subgroup.zpowers_le.mpr htX))
  have hP2 : IsPGroup 2 (blockZ K ⊓ Zt : Subgroup G) :=
    (pCoreOf_isPGroup 2 K).to_le (inf_le_left.trans (inf_le_left.trans
      (commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K))))
  have hN := isUniqueM_normalizer_le sk.lemma_4_3_5 hne hP2 hX
  have hKX : K ≤ Subgroup.normalizer ((blockZ K ⊓ Zt : Subgroup G) : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ hz =>
      (Subgroup.mem_centralizer_iff.mp hz.1.2 k hk).symm)
  exact sk.not_le (le_inf (le_of_mem_cComp sk.cComp) (hKX.trans hN))

theorem not_map_conj_blockU_le_centralizer (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hchar : CharTwo K)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Hm : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥K →* ↥Hm}
    {β : ↥(blockU K) →* Multiplicative (ι → F)} (hb : IsMatrixBlockTypeWith K Hm α β) :
    ¬ (blockU K).map (MulAut.conj t).toMonoidHom ≤
      Subgroup.centralizer (blockU K : Set G) := by
  intro hle
  apply sk.not_commutator_conj_blockU_le hR hC h37 h38 h39 hchar
  refine Subgroup.commutator_le.mpr fun x hx k hk => ?_
  obtain ⟨u, hu, rfl⟩ := hx
  have huS : u ∈ T ⊓ H := sk.pCoreOf_K_le_S hR hC h37 h38 h39
    (commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K) hu)
  have hxS : (MulAut.conj t).toMonoidHom u ∈ T ⊓ H := by
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp sk.t_normalizer u).mp huS
  exact Sp4Z.commutator_mem_pCoreOf hb (sk.S_le_normalizer hxS) (hle ⟨u, hu, rfl⟩) hk

end Setting432K

end CFSG.Quasithin.H13.Ch4
