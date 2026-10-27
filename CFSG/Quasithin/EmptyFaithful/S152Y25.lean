module

public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType

namespace S152Y

theorem pCore_two_eq_comap {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    CFSG.Open.pCore 2 A = (CFSG.Open.pCore 2 B).comap f := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mp (BorelTits.map_pCore_le 2 f hf)
  · have hn : ((CFSG.Open.pCore 2 B).comap f).Normal := (BorelTits.pCore_normal 2).comap f
    have hp : IsPGroup 2 ((CFSG.Open.pCore 2 B).comap f) := by
      intro y
      obtain ⟨k, hk⟩ := (BorelTits.pCore_isPGroup (G := B) 2) ⟨f (y : A), y.2⟩
      have h1 : f ((y : A) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      obtain ⟨j, hj⟩ := hker ⟨(y : A) ^ 2 ^ k, MonoidHom.mem_ker.mpr h1⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simpa [pow_add, pow_mul] using this
    exact BorelTits.le_pCore 2 hn hp

theorem nonempty_quot_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty ((A ⧸ CFSG.Open.pCore 2 A) ≃* (B ⧸ CFSG.Open.pCore 2 B)) := by
  have hcore := pCore_two_eq_comap f hf hker
  let g : A →* B ⧸ CFSG.Open.pCore 2 B := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = CFSG.Open.pCore 2 A := by
    rw [hcore]
    ext x
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

variable {G : Type*} [Group G] [Finite G]

theorem nonempty_oTwoQuot_equiv_image {M P : Subgroup G} (hPM : P ≤ M)
    {P' : Subgroup (OTwoQuot M)} (hP' : P' = imageOTwoQuot M P) :
    Nonempty (OTwoQuot P ≃* OTwoQuot P') := by
  subst hP'
  let f : ↥P →* ↥(imageOTwoQuot M P) :=
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (Subgroup.inclusion hPM)).codRestrict _
      (fun x => ⟨⟨(x : G), hPM x.2⟩, by simp [Subgroup.mem_subgroupOf], rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨u, y, hy, rfl⟩
    exact ⟨⟨(y : G), hy⟩, Subtype.ext rfl⟩
  have hker : IsPGroup 2 f.ker := by
    intro x
    have hx : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)) (Subgroup.inclusion hPM (x : ↥P)) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    have hmem : Subgroup.inclusion hPM (x : ↥P) ∈ CFSG.Open.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (BorelTits.pCore_isPGroup (G := ↥M) 2) ⟨_, hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : CFSG.Open.pCore 2 ↥M => ((z : ↥M) : G)) hk
    simpa using this
  exact nonempty_quot_equiv f hf hker

end S152Y

end CFSG.Quasithin
