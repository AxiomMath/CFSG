module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCover
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.CGT.PushingUpLit.CGT6X.End4Cover

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_ordinaryModel
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hodd6 : m = 6 → Odd (Nat.card (Subgroup.center ↥L))) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (ψ : Su F0 2 1 m →* G),
      Nat.card F0 = 4 ∧ QTwoOrdModel Bs L ψ := by
  classical
  letI : Field hFrameL.F0 := hFrameL.fieldF0
  letI : Finite hFrameL.F0 := hFrameL.finiteF0
  letI : CharP hFrameL.F0 2 := hFrameL.charF0
  letI : Fact (Nat.Prime 2) := hFrameL.factF0
  letI : Group hFrameL.L0 := hFrameL.groupL0
  cases hFm
  have hK : Nat.card hFrameL.F0 = (2 ^ 1) ^ 2 := by
    rw [hFrameL.hcardF0]; norm_num
  have hm5 : 5 ≤ hFrameL.m := hFrameL.hm
  have hm4 : 4 ≤ hFrameL.m := by omega
  have hm3 : 3 ≤ hFrameL.m := by omega
  have hne4 : hFrameL.m ≠ 4 := by omega
  have hSS : LargeEvenSStar 3 B x L := S.hcfg.1.1.1.2.2.2.2.2.2.1
  haveI hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.2 hSS.2.2.2.1.2.2.1
  haveI hperfSu : Group.IsPerfect (Su hFrameL.F0 2 1 hFrameL.m) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK)
      hm3 (fun h => by omega)
  have hlift : ∃ ψ₀ : Su hFrameL.F0 2 1 hFrameL.m →* ↥L,
      (∀ u, hFrameL.c (ψ₀ u) = hFrameL.πSU u) ∧ Function.Surjective ψ₀ := by
    by_cases hm6 : hFrameL.m = 6
    ·
      have hkerbot : hFrameL.c.ker = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        have hodd : Odd (Nat.card (Subgroup.center ↥L)) := hodd6 hm6
        have hdvd : Nat.card hFrameL.c.ker ∣ Nat.card (Subgroup.center ↥L) :=
          Subgroup.card_dvd_of_le hFrameL.hc_ker
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hFrameL.hc_two
        have hk0 : k = 0 := by
          by_contra hk0
          have h2 : 2 ∣ Nat.card hFrameL.c.ker := by rw [hk]; exact dvd_pow_self 2 hk0
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
        rw [hk0, pow_zero] at hk
        exact hk
      have hinj : Function.Injective hFrameL.c := (MonoidHom.ker_eq_bot_iff _).mp hkerbot
      let e : ↥L ≃* hFrameL.L0 := MulEquiv.ofBijective hFrameL.c ⟨hinj, hFrameL.hc_surj⟩
      exact ⟨e.symm.toMonoidHom.comp hFrameL.πSU,
        fun u => e.apply_symm_apply (hFrameL.πSU u),
        e.symm.surjective.comp hFrameL.hπ_surj⟩
    ·
      have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* Su hFrameL.F0 2 1 hFrameL.m),
          Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
            ∃ σ : Su hFrameL.F0 2 1 hFrameL.m →* E, ∀ u, π (σ u) = u := by
        intro E _ _ π hπ hker _
        obtain ⟨σ, hσ⟩ := ggSU_central_extension_splits hFrameL.F0 1 hFrameL.m hK
          hm4 (by rintro ⟨h, -⟩; exact hne4 h)
          (by rintro ⟨h, -⟩; exact hm6 h) E π hπ hker
        exact ⟨σ, fun u => DFunLike.congr_fun hσ u⟩
      obtain ⟨ψ₀, hψ₀, hsurj, -⟩ :=
        CFSG.LieType.Steinberg.exists_surjective_of_isPerfect (K := Su hFrameL.F0 2 1 hFrameL.m)
          (Q := hFrameL.L0) (P := ↥L) (β := hFrameL.πSU) (η := hFrameL.c)
          hsplit hFrameL.hπ_surj hFrameL.hc_surj hFrameL.hc_ker hFrameL.hc_two
      exact ⟨ψ₀, hψ₀, hsurj⟩
  obtain ⟨ψ₀, hψ₀c, hψ₀surj⟩ := hlift
  let ψ : Su hFrameL.F0 2 1 hFrameL.m →* G := L.subtype.comp ψ₀
  have hrange : ψ.range = L := by
    rw [show ψ = L.subtype.comp ψ₀ from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hψ₀surj, Subgroup.map_top, Subgroup.range_subtype]
  have hker : ψ.ker ≤ Subgroup.center (Su hFrameL.F0 2 1 hFrameL.m) := by
    intro u hu
    apply hFrameL.hπ_ker
    rw [MonoidHom.mem_ker]
    have hu1 : ψ₀ u = 1 := by
      apply Subtype.ext
      exact hu
    rw [← hψ₀c u, hu1, map_one]
  have hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin hFrameL.m) hFrameL.F0, ggIsDiagMat g ∧
      ∀ u : Su hFrameL.F0 2 1 hFrameL.m, ∃ u' : Su hFrameL.F0 2 1 hFrameL.m,
        (u' : GL (Fin hFrameL.m) hFrameL.F0) =
          g * (u : GL (Fin hFrameL.m) hFrameL.F0) * g⁻¹ ∧
          ψ u' = (b : G) * ψ u * (b : G)⁻¹ := by
    intro b
    obtain ⟨g, hgdiag, hgu⟩ := hFrameL.hdiag b
    let α : Su hFrameL.F0 2 1 hFrameL.m →* Su hFrameL.F0 2 1 hFrameL.m :=
      MonoidHom.mk' (fun u => (hgu u).choose) (by
        intro u v
        apply Subtype.ext
        calc (((hgu (u * v)).choose : Su hFrameL.F0 2 1 hFrameL.m) :
              GL (Fin hFrameL.m) hFrameL.F0)
            = g * ((u * v : Su hFrameL.F0 2 1 hFrameL.m) :
                GL (Fin hFrameL.m) hFrameL.F0) * g⁻¹ :=
              ((hgu (u * v)).choose_spec).1
          _ = (g * (u : GL (Fin hFrameL.m) hFrameL.F0) * g⁻¹) *
              (g * (v : GL (Fin hFrameL.m) hFrameL.F0) * g⁻¹) := by
              rw [Subgroup.coe_mul]; group
          _ = (((hgu u).choose : Su hFrameL.F0 2 1 hFrameL.m) :
                GL (Fin hFrameL.m) hFrameL.F0) *
              (((hgu v).choose : Su hFrameL.F0 2 1 hFrameL.m) :
                GL (Fin hFrameL.m) hFrameL.F0) := by
              rw [((hgu u).choose_spec).1, ((hgu v).choose_spec).1])
    have hαcoe : ∀ u,
        ((α u : Su hFrameL.F0 2 1 hFrameL.m) : GL (Fin hFrameL.m) hFrameL.F0) =
          g * (u : GL (Fin hFrameL.m) hFrameL.F0) * g⁻¹ :=
      fun u => ((hgu u).choose_spec).1
    have hαρ : ∀ u, hFrameL.ρ b (hFrameL.πSU u) = hFrameL.πSU (α u) :=
      fun u => ((hgu u).choose_spec).2
    let β : ↥L →* ↥L :=
      { toFun := fun l => ⟨(b : G) * (l : G) * (b : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hFrameL.hBsN b.2) l).mp l.2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by
          intro y z
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group }
    let f : Su hFrameL.F0 2 1 hFrameL.m →* ↥L := ψ₀.comp α
    let h : Su hFrameL.F0 2 1 hFrameL.m →* ↥L := β.comp ψ₀
    have hcent : ∀ u, h u * (f u)⁻¹ ∈ Subgroup.center ↥L := by
      intro u
      apply hFrameL.hc_ker
      have h1 : hFrameL.c (f u) = hFrameL.πSU (α u) := hψ₀c (α u)
      have h2 : hFrameL.c (h u) = hFrameL.ρ b (hFrameL.πSU u) := by
        have hβ := hFrameL.hρ_induced b (ψ₀ u)
        rw [hψ₀c u] at hβ
        exact hβ
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, hαρ u, mul_inv_cancel]
    have hhf : h = f := CFSG.CGT.PushingUpLit.CGT6X.End4.hom_eq_of_central h f hcent
    refine ⟨g, hgdiag, fun u => ⟨α u, hαcoe u, ?_⟩⟩
    have hfh' : ψ₀ (α u) = β (ψ₀ u) := (DFunLike.congr_fun hhf u).symm
    change ((ψ₀ (α u) : ↥L) : G) = (b : G) * ((ψ₀ u : ↥L) : G) * (b : G)⁻¹
    rw [hfh']
    rfl
  refine ⟨hFrameL.F0, hFrameL.fieldF0, hFrameL.finiteF0, hFrameL.charF0, ψ,
    hFrameL.hcardF0, hrange, hker, hdiag⟩

end CFSG.StandardType.QTwo

end
