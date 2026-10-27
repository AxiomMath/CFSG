module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126f
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Pa
public import CFSG.Quasithin.Vol2.Ch12Sec6L33e

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S126 F126 L1233
open CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G] {T K H : Subgroup G} {W : Type} [CommGroup W]

section Action

variable (hXH : K ⊔ T ≤ H) (ρ : ↥(K ⊔ T) →* MulAut W)

@[expose] noncomputable def starOf (x : ↥(K ⊔ T)) : S126.HStar H :=
  QuotientGroup.mk (⟨x, hXH x.2⟩ : ↥H)

theorem starOf_mul (x y : ↥(K ⊔ T)) : starOf hXH (x * y) = starOf hXH x * starOf hXH y := rfl

theorem starOf_inv (x : ↥(K ⊔ T)) : starOf hXH x⁻¹ = (starOf hXH x)⁻¹ := rfl

theorem starOf_pow (x : ↥(K ⊔ T)) (n : ℕ) : starOf hXH (x ^ n) = starOf hXH x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, starOf_mul, ih, pow_succ]

variable {hXH ρ}

theorem rho_mem_of_starOf_mem (hρQ : ∀ x : ↥(K ⊔ T), (x : G) ∈ pCoreOf 2 H → ρ x = 1)
    {x : ↥(K ⊔ T)} (hx : starOf hXH x ∈ S126.star H K) :
    ρ x ∈ (K.subgroupOf (K ⊔ T)).map ρ := by
  obtain ⟨⟨k, hkH⟩, hk, he⟩ := hx
  have hkK : k ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hkX : k ∈ K ⊔ T := Subgroup.mem_sup_left hkK
  have hq := mem_pCoreOf_of_mk_eq (x := ⟨k, hkH⟩) (y := ⟨x, hXH x.2⟩) he
  have h1 : ρ (⟨k, hkX⟩⁻¹ * x) = 1 := hρQ _ hq
  refine ⟨⟨k, hkX⟩, hkK, ?_⟩
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem starOf_mem_centralizer (hKn : (S126.star H K).Normal)
    (hperf : ⁅S126.star H K, S126.star H K⁆ = S126.star H K)
    (hXK : ∀ x ∈ K ⊔ T, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hρK : ∀ x : ↥(K ⊔ T), (x : G) ∈ K → ρ x = 1 →
      ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    {x : ↥(K ⊔ T)} (hx : ∀ k : ↥(K ⊔ T), (k : G) ∈ K → ρ x * ρ k = ρ k * ρ x) :
    starOf hXH x ∈ Subgroup.centralizer (S126.star H K : Set (S126.HStar H)) := by
  have hc : ∀ l ∈ S126.star H K, starOf hXH x * l * (starOf hXH x)⁻¹ * l⁻¹ ∈ S126.star H K :=
    fun l hl => (S126.star H K).mul_mem (hKn.conj_mem l hl _) ((S126.star H K).inv_mem hl)
  have hz : ∀ l ∈ S126.star H K, ∀ m ∈ S126.star H K,
      Commute (starOf hXH x * l * (starOf hXH x)⁻¹ * l⁻¹) m := by
    rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩ _ ⟨⟨k', hk'H⟩, hk', rfl⟩
    have hkK : k ∈ K := Subgroup.mem_subgroupOf.1 hk
    have hk'K : k' ∈ K := Subgroup.mem_subgroupOf.1 hk'
    set kX : ↥(K ⊔ T) := ⟨k, Subgroup.mem_sup_left hkK⟩
    set k'X : ↥(K ⊔ T) := ⟨k', Subgroup.mem_sup_left hk'K⟩
    set c : ↥(K ⊔ T) := x * kX * x⁻¹ * kX⁻¹ with hcdef
    have hcK : (c : G) ∈ K := K.mul_mem (hXK _ x.2 k hkK) (K.inv_mem hkK)
    have hc1 : ρ c = 1 := by
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hx kX hkK]
      group
    set d : ↥(K ⊔ T) := c * k'X * c⁻¹ * k'X⁻¹ with hddef
    have hq : (d : G) ∈ pCoreOf 2 H := hρK c hcK hc1 k' hk'K
    have hd1 : starOf hXH d = 1 := mkH_eq_one_iff.2 hq
    have hd : starOf hXH d = starOf hXH c * starOf hXH k'X * (starOf hXH c)⁻¹ *
        (starOf hXH k'X)⁻¹ := rfl
    show Commute (starOf hXH c) (starOf hXH k'X)
    rw [hd] at hd1
    calc starOf hXH c * starOf hXH k'X =
        (starOf hXH c * starOf hXH k'X * (starOf hXH c)⁻¹ * (starOf hXH k'X)⁻¹) *
          (starOf hXH k'X * starOf hXH c) := by group
      _ = starOf hXH k'X * starOf hXH c := by rw [hd1, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (commute_of_conj_mul_inv_central hperf hc hz l hl).eq.symm

end Action

section Hom

variable {ρ : ↥(K ⊔ T) →* MulAut W}

theorem exists_star_hom (hKH : K ≤ H)
    (hρQ : ∀ x : ↥(K ⊔ T), (x : G) ∈ pCoreOf 2 H → ρ x = 1)
    (hρK : ∀ x : ↥(K ⊔ T), (x : G) ∈ K → ρ x = 1 →
      ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∃ θ : ↥(S126.star H K) →* ↥((K.subgroupOf (K ⊔ T)).map ρ), Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center ↥(S126.star H K) := by
  let g : ↥K →* ↥(S126.star H K) :=
    { toFun := fun k => ⟨QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H),
        ⟨⟨k, hKH k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : ↥K →* ↥((K.subgroupOf (K ⊔ T)).map ρ) :=
    { toFun := fun k => ⟨ρ ⟨k, Subgroup.mem_sup_left k.2⟩,
        ⟨⟨k, Subgroup.mem_sup_left k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ ⟨a, Subgroup.mem_sup_left a.2⟩
        ⟨b, Subgroup.mem_sup_left b.2⟩) }
  have hgs : Function.Surjective g := by
    rintro ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨_, ⟨⟨k, hkX⟩, hk, rfl⟩⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  have hle : g.ker ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have h1 : (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) : S126.HStar H) = 1 :=
      congrArg Subtype.val hk
    exact Subtype.ext (hρQ ⟨k, Subgroup.mem_sup_left k.2⟩ (mkH_eq_one_iff.1 h1))
  let e := QuotientGroup.quotientKerEquivOfSurjective g hgs
  let θ : ↥(S126.star H K) →* ↥((K.subgroupOf (K ⊔ T)).map ρ) :=
    (QuotientGroup.lift g.ker f hle).comp e.symm.toMonoidHom
  have hθ : ∀ k : ↥K, θ (g k) = f k := by
    intro k
    have he : e.symm (g k) = QuotientGroup.mk k := e.symm_apply_eq.2 rfl
    show QuotientGroup.lift g.ker f hle (e.symm (g k)) = f k
    rw [he, QuotientGroup.lift_mk]
  refine ⟨θ, fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨k, rfl⟩ := hfs y
    exact ⟨g k, hθ k⟩
  · obtain ⟨k, rfl⟩ := hgs y
    have hfk : f k = 1 := by
      rw [← hθ k]
      exact hy
    have hρk : ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1 := congrArg Subtype.val hfk
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, ⟨⟨k', hk'H⟩, hk', rfl⟩⟩
    have hk'K : k' ∈ K := Subgroup.mem_subgroupOf.1 hk'
    have hq := hρK ⟨k, Subgroup.mem_sup_left k.2⟩ k.2 hρk k' hk'K
    apply Subtype.ext
    have h1 : (QuotientGroup.mk (⟨(k : G) * k' * (k : G)⁻¹ * k'⁻¹,
        H.mul_mem (H.mul_mem (H.mul_mem (hKH k.2) hk'H) (H.inv_mem (hKH k.2)))
          (H.inv_mem hk'H)⟩ : ↥H) : S126.HStar H) = 1 := mkH_eq_one_iff.2 hq
    have h2 : (QuotientGroup.mk (⟨(k : G) * k' * (k : G)⁻¹ * k'⁻¹,
        H.mul_mem (H.mul_mem (H.mul_mem (hKH k.2) hk'H) (H.inv_mem (hKH k.2)))
          (H.inv_mem hk'H)⟩ : ↥H) : S126.HStar H) =
        (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) : S126.HStar H) * QuotientGroup.mk ⟨k', hk'H⟩ *
          (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H))⁻¹ * (QuotientGroup.mk ⟨k', hk'H⟩)⁻¹ := rfl
    rw [h2] at h1
    show QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k', hk'H⟩ * QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) =
      QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k', hk'H⟩
    rw [QuotientGroup.mk'_apply]
    calc (QuotientGroup.mk ⟨k', hk'H⟩ : S126.HStar H) * QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) =
        ((QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) : S126.HStar H) * QuotientGroup.mk ⟨k', hk'H⟩ *
          (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H))⁻¹ * (QuotientGroup.mk ⟨k', hk'H⟩)⁻¹)⁻¹ *
            (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) * QuotientGroup.mk ⟨k', hk'H⟩) := by group
      _ = QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) * QuotientGroup.mk ⟨k', hk'H⟩ := by
        rw [h1, inv_one, one_mul]

end Hom

end CFSG.Quasithin.H13.L1232
