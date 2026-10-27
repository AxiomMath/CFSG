module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem centralizer_mem_of_perfect_action614 {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    (hperf : Group.IsPerfect ↥L) {g : Γ} (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    (α : ↥L → ↥L) (hα : ∀ k : ↥L, (α k : Γ) = g * k * g⁻¹)
    (hz : ∀ k : ↥L, (α k)⁻¹ * k ∈ Subgroup.center ↥L) :
    g ∈ Subgroup.centralizer (L : Set Γ) := by
  have hα_mul : ∀ a b : ↥L, α (a * b) = α a * α b := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hα]
    group
  have hf_mul : ∀ a b : ↥L, (α (a * b))⁻¹ * (a * b) = ((α a)⁻¹ * a) * ((α b)⁻¹ * b) := by
    intro a b
    have hc := Subgroup.mem_center_iff.mp (hz a) ((α b)⁻¹)
    rw [hα_mul, mul_inv_rev]
    calc (α b)⁻¹ * (α a)⁻¹ * (a * b) = (α b)⁻¹ * ((α a)⁻¹ * a) * b := by group
      _ = ((α a)⁻¹ * a) * (α b)⁻¹ * b := by rw [hc]
      _ = ((α a)⁻¹ * a) * ((α b)⁻¹ * b) := by group
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun k => ⟨(α k)⁻¹ * k, hz k⟩) (fun a b => Subtype.ext (hf_mul a b))
  have hker := Abelianization.commutator_subset_ker f
  rw [hperf.commutator_eq_top] at hker
  have hf : ∀ k : ↥L, f k = 1 := fun k => MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k))
  have hαk : ∀ k : ↥L, α k = k := fun k => by
    have h2 : (α k)⁻¹ * k = 1 := congrArg Subtype.val (hf k)
    exact inv_mul_eq_one.mp h2
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have e : g * k * g⁻¹ = k := by
    have h3 := congrArg Subtype.val (hαk ⟨k, hk⟩)
    rw [hα] at h3
    exact h3
  have hgk : g * k = k * g := by
    calc g * k = g * k * g⁻¹ * g := by group
      _ = k * g := by rw [e]
  exact hgk.symm

section Lev

variable {G : Type} [Group G] {K : Subgroup G} {u : G} {p : ℕ}

theorem IsL3Levi.mem_center_iff (h : IsL3Levi K u p) (x : ↥K) :
    x ∈ Subgroup.center ↥K ↔ (x : G) = 1 ∨ (x : G) = u :=
  h.2.2.1 x

theorem IsL3Levi.pCore_eq_center (hp : p.Prime) (hp5 : 5 ≤ p) (h : IsL3Levi K u p) :
    CFSG.pCore 2 ↥K = Subgroup.center ↥K := by
  obtain ⟨hu2, -, hcen, -, F, hF, hFin, hcard, ⟨ψ⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥K) := by
    intro x
    refine ⟨1, ?_⟩
    have hx : ((x : ↥K) : G) ^ 2 = 1 := by
      rcases (hcen x.1).mp x.2 with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, ← hu2]
        exact pow_orderOf_eq_one u
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx
  have hge : Subgroup.center ↥K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨inferInstance, hZ2⟩
  refine le_antisymm ?_ hge
  let θ : ↥K →* PSL2 F := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨z, rfl⟩ := ψ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) z
    exact ⟨x, rfl⟩
  haveI hQn : ((CFSG.pCore 2 ↥K).map θ).Normal := Subgroup.Normal.map inferInstance θ hθs
  have hsimple : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  haveI : Nontrivial (PSL2 F) := hsimple.toNontrivial
  rcases hsimple.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map θ) with hbot | htop
  · intro x hx
    have h1 : θ x ∈ (CFSG.pCore 2 ↥K).map θ := Subgroup.mem_map_of_mem θ hx
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : ψ (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K) = 1 := h1
    exact (QuotientGroup.eq_one_iff x).mp ((MulEquiv.map_eq_one_iff ψ).mp h2)
  · exfalso
    have hPG : IsPGroup 2 (PSL2 F) := by
      intro g
      have hg : g ∈ (CFSG.pCore 2 ↥K).map θ := by
        rw [htop]
        exact Subgroup.mem_top g
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨x, hx⟩
      have hx1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      rw [← map_pow, hx1, map_one]
    haveI : Finite (PSL2 F) := inferInstance
    have hnt := IsPGroup.center_nontrivial hPG
    rw [psl2_center_eq_bot F] at hnt
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact hab (Subtype.ext ((Subgroup.mem_bot.mp a.2).trans (Subgroup.mem_bot.mp b.2).symm))

theorem IsL3Levi.exists_equiv_psl2 (hp : p.Prime) (hp5 : 5 ≤ p) (h : IsL3Levi K u p) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      Nonempty (ModO2 K ≃* PSL2 F) := by
  have hpc : CFSG.pCore 2 ↥K = Subgroup.center ↥K := IsL3Levi.pCore_eq_center hp hp5 h
  obtain ⟨-, -, -, -, F, hF, hFin, hcard, ⟨ψ⟩⟩ := h
  exact ⟨F, hF, hFin, hcard, ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans ψ⟩⟩

theorem IsL3Levi.exists_action (hp : p.Prime) (hp5 : 5 ≤ p) (h : IsL3Levi K u p) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : ↥(Subgroup.normalizer (K : Set G)) →* PGammaL2 F),
      Nat.card F = p ∧
      (∀ (g : G) (hg : g ∈ K), σ ⟨g, Subgroup.le_normalizer hg⟩ ∈ pGammaL2PSLRange F) ∧
      (∀ x ∈ pGammaL2PSLRange F, ∃ (g : G) (hg : g ∈ K), σ ⟨g, Subgroup.le_normalizer hg⟩ = x) ∧
      (∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)), σ ⟨g, hg⟩ = 1 →
        g ∈ Subgroup.centralizer (K : Set G)) := by
  have hpc : CFSG.pCore 2 ↥K = Subgroup.center ↥K := IsL3Levi.pCore_eq_center hp hp5 h
  have hperf : Group.IsPerfect ↥K := by
    obtain ⟨-, -, -, hpf, -⟩ := h
    exact hpf
  obtain ⟨F, hF, hFin, hcard, ⟨ϕ⟩⟩ := IsL3Levi.exists_equiv_psl2 hp hp5 h
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_refl 1, by rw [hcard, pow_one]⟩
  have hcardF : 3 < Nat.card F := by
    rw [hcard]
    omega
  have hF1 : Nat.card F = p ^ 1 := by rw [hcard, pow_one]
  let Ψ : MulAut (ModO2 K) ≃* PGammaL2 F :=
    (MulAut.congr ϕ).trans (pGammaL2EquivMulAut614 F hK hcardF hF1).symm
  have hΨ : ((MulAut.conj : ModO2 K →* MulAut (ModO2 K)).range).map Ψ.toMonoidHom =
      pGammaL2PSLRange F := by
    have e : Ψ.toMonoidHom = (pGammaL2EquivMulAut614 F hK hcardF hF1).symm.toMonoidHom.comp
        (MulAut.congr ϕ).toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, map_mulAut_congr614, map_pGammaL2EquivMulAut614]
  refine ⟨F, hF, hFin, Ψ.toMonoidHom.comp (actModO2_614 K), hcard, ?_, ?_, ?_⟩
  ·
    intro g hg
    rw [← hΨ]
    refine Subgroup.mem_map.mpr ⟨MulAut.conj ((⟨g, hg⟩ : ↥K) : ModO2 K),
      MonoidHom.mem_range.mpr ⟨((⟨g, hg⟩ : ↥K) : ModO2 K), rfl⟩, ?_⟩
    show Ψ (MulAut.conj ((⟨g, hg⟩ : ↥K) : ModO2 K)) =
      Ψ (actModO2_614 K ⟨g, Subgroup.le_normalizer hg⟩)
    rw [actModO2_614_of_mem K hg]
  ·
    intro x hx
    rw [← hΨ] at hx
    obtain ⟨φ, hφ, hxφ⟩ := Subgroup.mem_map.mp hx
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hφ
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨(k : G), k.2, ?_⟩
    rw [← hxφ]
    show Ψ (actModO2_614 K ⟨(k : G), Subgroup.le_normalizer k.2⟩) =
      Ψ (MulAut.conj (k : ModO2 K))
    rw [actModO2_614_of_mem K k.2]
  ·
    intro g hg hσ
    have hσ' : Ψ (actModO2_614 K ⟨g, hg⟩) = 1 := hσ
    have hact : actModO2_614 K ⟨g, hg⟩ = 1 := (MulEquiv.map_eq_one_iff Ψ).mp hσ'
    refine centralizer_mem_of_perfect_action614 hperf hg
      (fun k => ⟨g * (k : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp k.2⟩)
      (fun k => rfl) ?_
    intro k
    rw [← hpc]
    have h1 : actModO2_614 K ⟨g, hg⟩ (k : ModO2 K) = (1 : MulAut (ModO2 K)) (k : ModO2 K) := by
      rw [hact]
    rw [actModO2_614_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1

end Lev

end CFSG.Quasithin.H13
