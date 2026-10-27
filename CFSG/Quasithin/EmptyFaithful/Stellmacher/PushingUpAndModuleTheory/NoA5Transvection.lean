module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepA

public section

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Quasithin.F53Mod CFSG.Open CFSG.QuasithinUnique Equiv

theorem noA5Transvection_holds : NoA5Transvection := by
  intro G _ _ X V ψ hψ hker hVQ hXN hV hC s hs hs1 hs2 hsA
  have hYcomm := isMulCommutative_subgroup_iff.mp hV.1
  have hsec : IsSec X ⊥ V :=
    { le := bot_le
      normN := hXN
      normL := fun x _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl; simp
        · intro h1
          have : h = x⁻¹ * (x * h * x⁻¹) * x := by group
          rw [this, h1]; simp
      comm := fun x hx y hy => by
        rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact (hYcomm x hx y hy)
      sq := fun x hx => by rw [Subgroup.mem_bot]; exact hV.2 x hx }
  have hcent : ∀ (f : G) (hf : f ∈ X), (∀ y ∈ V, f * y * f⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G)) ↔
      ψ ⟨f, hf⟩ = 1 := by
    intro f hf
    rw [hker ⟨f, hf⟩, ← hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨hf, fun y hy => ?_⟩
      have := h y hy
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · rintro ⟨-, h⟩ y hy
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact (h y hy).symm
  have hk : ψ.ker ≤ (cSecIn X ⊥ V).subgroupOf X := by
    intro f hf
    rw [Subgroup.mem_subgroupOf]
    refine (mem_cSecIn_iff (fun x _ => ?_)).mpr ⟨f.2, (hcent f f.2).mpr (MonoidHom.mem_ker.mp hf)⟩
    exact hsec.normL ‹_›
  set M := secModule hsec ψ hψ hk with hM
  have hfaith : M.Faithful := by
    rw [hM, secModule_faithful_iff]
    intro f hf
    rw [MonoidHom.mem_ker]
    obtain ⟨hfX, hfc⟩ :=
      (mem_cSecIn_iff (fun x _ => hsec.normL ‹_›)).mp (Subgroup.mem_subgroupOf.mp hf)
    exact (hcent f hfX).mp hfc
  have hnt : fixW M (alternatingGroup (Fin 5)) ≠ ⊤ := by
    intro htop
    apply hs1
    apply hfaith
    rw [map_one]
    ext w
    exact (eq_top_iff.mp htop (Subgroup.mem_top w)) _ hsA
  have hs5 : (ψ ⟨s, hs⟩) ^ 5 ≠ 1 := by
    intro h
    apply hs1
    have : ψ ⟨s, hs⟩ ^ 5 = ψ ⟨s, hs⟩ := by
      calc ψ ⟨s, hs⟩ ^ 5 = (ψ ⟨s, hs⟩ ^ 2) ^ 2 * ψ ⟨s, hs⟩ := by group
        _ = ψ ⟨s, hs⟩ := by rw [hs2]; simp
    rw [← this]; exact h
  have h4 := cf_small M hnt hsA hs1 hs5
  have hSX : Subgroup.zpowers s ≤ X := Subgroup.zpowers_le.mpr hs
  have hrange : (ψ.comp (Subgroup.inclusion hSX)).range = Subgroup.zpowers (ψ ⟨s, hs⟩) := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
      refine ⟨k, ?_⟩
      rw [← map_zpow]
      show _ = ψ ⟨(y : G), hSX y.2⟩
      congr 1
      exact Subtype.ext (by simpa using hk)
    · rintro ⟨k, rfl⟩
      refine ⟨⟨s ^ k, Subgroup.zpow_mem_zpowers s k⟩, ?_⟩
      rw [← map_zpow]
      show ψ ⟨s ^ k, _⟩ = _
      congr 1
  have hcen : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G) =
      Subgroup.centralizer ({s} : Set G) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h; exact h s (Subgroup.mem_zpowers s)
    · intro h g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute s x from h) k).eq
  have hidx := index_fixW_range hsec ψ hψ hk hSX
  rw [hrange, hcen] at hidx
  have : idx M (ψ ⟨s, hs⟩) = (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V := hidx
  omega

end CFSG.Quasithin.F53.Stellmacher
