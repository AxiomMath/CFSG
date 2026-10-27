module

public import CFSG.Quasithin.EmptyFaithful.S153XBlkA
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.X1469.Blk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.Quasithin.ModV
  CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {I S Iz K₁ K₂ : Subgroup G} {P : AppC.A5Pi K₁} {p : Fin 5} (X : Ctx I S Iz K₁ K₂ P p)
include X

theorem irred_E : ∀ N : Subgroup G, N ≤ Esub K₁ Iz →
    K₁ ⊓ Iz ≤ Subgroup.normalizer (N : Set G) → N ≤ Zsub S K₁ ∨ N = Esub K₁ Iz := by
  intro N hNE hYN
  by_cases hNZ : N ≤ Zsub S K₁
  · exact Or.inl hNZ
  right
  obtain ⟨n, hnN, hnZ⟩ := IsConcreteLE.not_le_iff_exists.mp hNZ
  obtain ⟨hnU, hnp⟩ := X.mem_E_iff.mp (hNE hnN)
  have hxe := (mem_evenWeight_iff _).mp (P.toPiData.bf n).2
  have hx0 : (P.toPiData.bf n).1 ≠ 0 := fun h => hnZ (X.mem_Z_iff.mpr ⟨hnU, Or.inl h⟩)
  have hx1 : (P.toPiData.bf n).1 ≠ zvec p := fun h => hnZ (X.mem_Z_iff.mpr ⟨hnU, Or.inr h⟩)
  have hconj : ∀ {σ : Perm (Fin 5)}, Perm.sign σ = 1 → σ p = p → ∃ m ∈ N, m ∈ blockU K₁ ∧
      (P.toPiData.bf m).1 = pact σ (P.toPiData.bf n).1 := by
    intro σ hσs hσp
    obtain ⟨y, hy, hpfy⟩ := X.exists_lift_Y hσs hσp
    have hyN : y ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hy.1
    refine ⟨y * n * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hYN hy) n).mp hnN,
      AppC.PiData.conj_mem_U hyN hnU, ?_⟩
    rw [P.toPiData.bf_conj hyN hnU, hpfy]
    rfl
  refine le_antisymm hNE fun e he => ?_
  obtain ⟨heU, hep⟩ := X.mem_E_iff.mp he
  by_cases h0 : (P.toPiData.bf e).1 = 0
  · have he1 : e = 1 := P.toPiData.bf_inj heU (one_mem _) (by rw [P.toPiData.bf_one]; exact Subtype.ext h0)
    rw [he1]
    exact one_mem N
  by_cases h1 : (P.toPiData.bf e).1 = zvec p
  · obtain ⟨σ, hσs, hσp, hsum⟩ := exists_sum_zvec p _ hxe hnp hx0 hx1
    obtain ⟨m, hmN, hmU, hbm⟩ := hconj hσs hσp
    have hem : e = n * m := by
      refine P.toPiData.bf_inj heU (mul_mem hnU hmU) (Subtype.ext ?_)
      rw [P.toPiData.bf_mul hnU hmU]
      show (P.toPiData.bf e).1 = (P.toPiData.bf n).1 + (P.toPiData.bf m).1
      rw [hbm, hsum, h1]
    rw [hem]
    exact mul_mem hnN hmN
  · obtain ⟨σ, hσs, hσp, hmap⟩ := exists_map_vanish p _ hxe hnp hx0 hx1 _
      ((mem_evenWeight_iff _).mp (P.toPiData.bf e).2) hep h0 h1
    obtain ⟨m, hmN, hmU, hbm⟩ := hconj hσs hσp
    have hem : e = m := P.toPiData.bf_inj heU hmU (Subtype.ext (by rw [hbm]; exact hmap))
    rw [hem]
    exact hmN

theorem fix_E : ∀ e ∈ Esub K₁ Iz, (∀ y ∈ K₁ ⊓ Iz, e * y * e⁻¹ * y⁻¹ ∈ Zsub S K₁) →
    e ∈ Zsub S K₁ := by
  intro e he h
  obtain ⟨heU, hep⟩ := X.mem_E_iff.mp he
  refine X.mem_Z_iff.mpr ⟨heU, ?_⟩
  by_contra hne
  obtain ⟨hne0, hne1⟩ := not_or.mp hne
  obtain ⟨σ, hσs, hσp, h1, h2⟩ :=
    exists_not_line p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf e).2) hep hne0 hne1
  obtain ⟨y, hy, hpfy⟩ := X.exists_lift_Y hσs hσp
  obtain ⟨-, hz⟩ := X.mem_Z_iff.mp (h y hy)
  rw [X.cfg.bf_comm P heU hy.1, hpfy] at hz
  rcases hz with hz | hz
  · exact h1 hz
  · exact h2 hz

theorem irred_B : ∀ N : Subgroup G, N ≤ S ⊓ K₁ → K₁ ⊓ Iz ≤ Subgroup.normalizer (N : Set G) →
    N ≤ blockU K₁ ∨ S ⊓ K₁ ≤ N ⊔ blockU K₁ := by
  intro N hNB hYN
  by_cases hNU : N ≤ blockU K₁
  · exact Or.inl hNU
  right
  obtain ⟨n, hnN, hnU⟩ := IsConcreteLE.not_le_iff_exists.mp hNU
  have hnB := hNB hnN
  have hv : P.toPiData.pf n ∈ klein p := (X.mem_S_iff hnB.2).mp hnB.1
  have hv1 : P.toPiData.pf n ≠ 1 := fun h => hnU (X.mem_U_of_pf hnB.2 h)
  intro b hb
  have hv' : P.toPiData.pf b ∈ klein p := (X.mem_S_iff hb.2).mp hb.1
  by_cases hb1 : P.toPiData.pf b = 1
  · exact Subgroup.mem_sup_right (X.mem_U_of_pf hb.2 hb1)
  obtain ⟨σ, hσs, hσp, hconj⟩ := exists_conj_klein p _ hv hv1 _ hv' hb1
  obtain ⟨y, hy, hpfy⟩ := X.exists_lift_Y hσs hσp
  have hyN : y ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hy.1
  have hnN' : n ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hnB.2
  have hm : y * n * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hYN hy) n).mp hnN
  have hmK : y * n * y⁻¹ ∈ K₁ := K₁.mul_mem (K₁.mul_mem hy.1 hnB.2) (K₁.inv_mem hy.1)
  have hmN : y * n * y⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hmK
  have hpf : P.toPiData.pf (y * n * y⁻¹) = P.toPiData.pf b := by
    rw [P.toPiData.pf_mul (mul_mem hyN hnN') (inv_mem hyN), P.toPiData.pf_mul hyN hnN',
      P.toPiData.pf_inv hyN, hpfy, hconj]
  have hu : (y * n * y⁻¹)⁻¹ * b ∈ blockU K₁ := by
    refine X.mem_U_of_pf (K₁.mul_mem (K₁.inv_mem hmK) hb.2) ?_
    rw [P.toPiData.pf_mul (inv_mem hmN) (Subgroup.le_normalizer hb.2), P.toPiData.pf_inv hmN, hpf,
      inv_mul_cancel]
  have e : b = (y * n * y⁻¹) * ((y * n * y⁻¹)⁻¹ * b) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hu)

theorem fix_B {c₁ : G} (hc₁ : c₁ ∈ K₁ ⊓ Iz) (hpf : P.toPiData.pf c₁ = gam p) :
    ∀ b ∈ S ⊓ K₁, (∀ y ∈ K₁ ⊓ Iz, b * y * b⁻¹ * y⁻¹ ∈ blockU K₁) → b ∈ blockU K₁ := by
  intro b hb h
  have hv : P.toPiData.pf b ∈ klein p := (X.mem_S_iff hb.2).mp hb.1
  refine X.mem_U_of_pf hb.2 (eq_one_of_comm_gam p _ hv ?_)
  have h1 := X.pf_U (h c₁ hc₁)
  rw [pf_comm P hb.2 hc₁.1, hpf] at h1
  exact h1

theorem gen_B {c₁ : G} (hc₁ : c₁ ∈ K₁) (hpf : P.toPiData.pf c₁ = gam p) :
    ∀ b ∈ S ⊓ K₁, ∃ b' ∈ S ⊓ K₁, ∃ u ∈ blockU K₁, b = (b' * c₁ * b'⁻¹ * c₁⁻¹) * u := by
  intro b hb
  have hv : P.toPiData.pf b ∈ klein p := (X.mem_S_iff hb.2).mp hb.1
  obtain ⟨v', hv', hvv⟩ := exists_comm_gam p _ hv
  obtain ⟨b', hb', hpfb'⟩ := X.exists_lift_B hv'
  have hgK : b' * c₁ * b'⁻¹ * c₁⁻¹ ∈ K₁ :=
    K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hb'.2 hc₁) (K₁.inv_mem hb'.2)) (K₁.inv_mem hc₁)
  have hgN : b' * c₁ * b'⁻¹ * c₁⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hgK
  refine ⟨b', hb', (b' * c₁ * b'⁻¹ * c₁⁻¹)⁻¹ * b,
    X.mem_U_of_pf (K₁.mul_mem (K₁.inv_mem hgK) hb.2) ?_, by group⟩
  rw [P.toPiData.pf_mul (inv_mem hgN) (Subgroup.le_normalizer hb.2), P.toPiData.pf_inv hgN,
    pf_comm P hb'.2 hc₁, hpfb', hpf, ← hvv, inv_mul_cancel]

theorem cent_B {c₁ : G} (hc₁ : c₁ ∈ K₁) (hpf : P.toPiData.pf c₁ = gam p) :
    ∀ u ∈ blockU K₁, (∀ b ∈ S ⊓ K₁,
      u * (b * c₁ * b⁻¹ * c₁⁻¹) = (b * c₁ * b⁻¹ * c₁⁻¹) * u) → u ∈ Zsub S K₁ := by
  intro u hu h
  refine X.mem_Z_iff.mpr ⟨hu, fix_klein p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf u).2)
    fun v hv => ?_⟩
  obtain ⟨v', hv', hvv⟩ := exists_comm_gam p _ hv
  obtain ⟨b, hb, hpfb⟩ := X.exists_lift_B hv'
  have hgK : b * c₁ * b⁻¹ * c₁⁻¹ ∈ K₁ :=
    K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hb.2 hc₁) (K₁.inv_mem hb.2)) (K₁.inv_mem hc₁)
  have h1 := (P.toPiData.comm_iff (Subgroup.le_normalizer hgK) hu).mp (h b hb).symm
  rw [pf_comm P hb.2 hc₁, hpfb, hpf, ← hvv] at h1
  exact congrArg Subtype.val h1

theorem centmod_B {c₁ : G} (hc₁ : c₁ ∈ K₁) (hpf : P.toPiData.pf c₁ = gam p) :
    ∀ u ∈ blockU K₁, (∀ b ∈ S ⊓ K₁,
      u * (b * c₁ * b⁻¹ * c₁⁻¹) * u⁻¹ * (b * c₁ * b⁻¹ * c₁⁻¹)⁻¹ ∈ Zsub S K₁) →
      u ∈ Esub K₁ Iz := by
  intro u hu h
  refine X.mem_E_iff.mpr ⟨hu, ?_⟩
  by_contra hne
  obtain ⟨v, hv, h1, h2⟩ :=
    exists_klein_not_line p _ ((mem_evenWeight_iff _).mp (P.toPiData.bf u).2) hne
  obtain ⟨v', hv', hvv⟩ := exists_comm_gam p _ hv
  obtain ⟨b, hb, hpfb⟩ := X.exists_lift_B hv'
  have hgK : b * c₁ * b⁻¹ * c₁⁻¹ ∈ K₁ :=
    K₁.mul_mem (K₁.mul_mem (K₁.mul_mem hb.2 hc₁) (K₁.inv_mem hb.2)) (K₁.inv_mem hc₁)
  obtain ⟨-, hz⟩ := X.mem_Z_iff.mp (h b hb)
  rw [X.cfg.bf_comm P hu hgK, pf_comm P hb.2 hc₁, hpfb, hpf, ← hvv] at hz
  rcases hz with hz | hz
  · exact h1 hz
  · exact h2 hz

end Ctx

end CFSG.Quasithin.X1469.Blk
