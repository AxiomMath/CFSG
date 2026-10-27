module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Self
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Witness
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

theorem ggF4_card_ge_pow_four
    (hRig : GGLabelRigidInput) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) (hf : 1 ≤ f) {R : Type} [Group R] [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) (hF4 : GGHasLabel ⟨.F4, 4, f⟩ R) {I : Set (MulAut R)}
    (hcent : GGF4CentAt p f R I) {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A)
    (hex : ∃ e ∈ A, ∃ J : Subgroup L', IsComponentOf J (ggFixSub e) ∧
      GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) :
    p ^ 4 ≤ Nat.card A := by
  obtain ⟨e, heA, J, hJ, hC3⟩ := hex
  have he1 : e ≠ 1 := by
    intro he
    subst he
    exact ggF4_fix_one_not_c3 hRig hf hnab hF4 ψ hψ hker hperf hJ hC3
  have hep : e ^ p = 1 := hA.2 e heA
  have hcomm : ∀ a ∈ A, e * a = a * e := by
    intro a ha
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨e, heA⟩ ⟨a, ha⟩)
  have hJa : ∀ a ∈ A, (∀ x ∈ J, a x ∈ J) ∧ ∃ j ∈ J, ∀ x ∈ J, a x = j * x * j⁻¹ := by
    intro a ha
    exact hcent L' ψ hψ hker hperf e a hep he1 (hcomm a ha) (hAI e heA) (hAI a ha) J hJ hC3
  have hstab : ∀ a ∈ A, ∀ l ∈ J, a l ∈ J := fun a ha l hl => (hJa a ha).1 l hl
  obtain ⟨res, hres⟩ := ggAutRestrictHom J A hstab
  have hA0 : IsElemAbelian p res.range := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨?comm⟩⟩
      intro x y
      apply Subtype.ext
      change x.val * y.val = y.val * x.val
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      rw [← ha, ← hb]
      rw [← map_mul, ← map_mul]
      congr 1
      exact hA.1.is_comm.comm a b
    · intro x hx
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      rw [← map_pow]
      have hap : a ^ p = 1 := Subtype.ext (hA.2 a.1 a.2)
      rw [hap, map_one]
  have hC3' : LargeEvenRawDatum ⟨.C, 3, f⟩
      (fun R _ I F => Nonempty (J ⧸ Subgroup.center J ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
    largeEvenRawDatum_inn_all hC3
  have hrank_raw := (kga_rank_label hp hp2 hpq) _ hC3'
  obtain ⟨R₃, instR₃, I₃, F₃, hQ₃⟩ := largeEvenRawDatum_exists hrank_raw
  obtain ⟨hQ₀₃, hrank₃⟩ := hQ₃
  obtain ⟨hR₃_iso, hInn₃⟩ := hQ₀₃
  obtain ⟨θ⟩ := hR₃_iso
  let ψ₃ : ↥J →* R₃ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  have hsurj : Function.Surjective ψ₃ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have hker₃ : ψ₃.ker ≤ Subgroup.center ↥J := by
    have hker_eq : ψ₃.ker = Subgroup.center ↥J := by
      dsimp [ψ₃]
      rw [← MonoidHom.comap_ker]
      rw [MonoidHom.ker_eq_bot (θ : ↥J ⧸ Subgroup.center ↥J →* R₃) (MulEquiv.injective θ)]
      rw [MonoidHom.comap_bot]
      exact QuotientGroup.ker_mk' _
    rw [hker_eq]
  have hperfJ : commutator ↥J = ⊤ := hJ.2.2.1
  have hA0_induces : ∀ a₀ ∈ res.range, ∃ φ ∈ I₃, ∀ l : ↥J, φ (ψ₃ l) = ψ₃ (a₀ l) := by
    intro a₀ ha₀
    obtain ⟨a, rfl⟩ := ha₀
    obtain ⟨j, hjJ, hj⟩ := (hJa a.1 a.2).2
    refine ⟨MulAut.conj (θ (QuotientGroup.mk ⟨j, hjJ⟩)), hInn₃ (Set.mem_range_self _), ?_⟩
    intro l
    change MulAut.conj (θ (QuotientGroup.mk ⟨j, hjJ⟩)) (θ (QuotientGroup.mk l)) =
      θ (QuotientGroup.mk ((res a) l))
    rw [MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    have hjl : (⟨j, hjJ⟩ : ↥J) * l * (⟨j, hjJ⟩ : ↥J)⁻¹ = (res a) l := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      exact ((hres a l).trans (hj l l.2)).symm
    change (QuotientGroup.mk' (Subgroup.center ↥J)) ⟨j, hjJ⟩ *
      (QuotientGroup.mk' (Subgroup.center ↥J)) l *
      ((QuotientGroup.mk' (Subgroup.center ↥J)) ⟨j, hjJ⟩)⁻¹ =
      (QuotientGroup.mk' (Subgroup.center ↥J)) ((res a) l)
    rw [← map_mul, ← map_inv, ← map_mul]
    exact congrArg _ hjl
  have hsc₀ : GGTorusSelfCent p res.range :=
    ggTorusSelfCent_restrict_image A J res hres hsc
  have hrank₃_app : p ^ 3 ≤ Nat.card res.range :=
    hrank₃ ↥J ψ₃ hsurj hker₃ hperfJ res.range hA0 hA0_induces hsc₀
  have he_ker : res ⟨e, heA⟩ = 1 := by
    ext l
    rw [hres ⟨e, heA⟩ l, MulAut.one_apply]
    exact mem_ggFixSub.mp (hJ.1 l.2)
  have hzpow_le : Subgroup.zpowers (⟨e, heA⟩ : A) ≤ res.ker := by
    rintro _ ⟨n, rfl⟩
    rw [MonoidHom.mem_ker, map_zpow, he_ker, one_zpow]
  have hker_ge : p ≤ Nat.card res.ker := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hle := Subgroup.card_le_of_le hzpow_le
    rwa [Nat.card_zpowers, Subgroup.orderOf_mk e heA, orderOf_eq_prime hep he1] at hle
  have hcard : Nat.card A = Nat.card res.ker * Nat.card res.range :=
    (Subgroup.card_ker_mul_card_range res).symm
  calc
    p ^ 4 = p * p ^ 3 := by ring
    _ ≤ Nat.card res.ker * Nat.card res.range := Nat.mul_le_mul hker_ge hrank₃_app
    _ = Nat.card A := hcard.symm

end KGA

end CFSG.StandardType

end
