module

public import Certificates.Certificate260393
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuPerm
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.Quasithin.B45Exc.Ru

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2

theorem ru_cent_checks :
    ruTCommCheck = true ∧ ruTSylCheck = true :=
  Certificates.certificate260393


theorem regIn_ruT : RegIn 4060 (ruP ⊓ Subgroup.centralizer {ruA0}) ruTGens := by
  intro r hr
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
  have hreg : RegIn 4060 ruP ruGens := regIn_ruP
  obtain ⟨g, hg, hgr⟩ := hreg.word w
  refine ⟨g, ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hgr⟩
  exact (eqA_iff (hgr.mul pRep_ruA0P).1 (pRep_ruA0P.mul hgr).1).1
    (List.all_eq_true.1 ru_cent_checks.1 _ hr)

theorem ru_cent_rank :
    ∀ B : Subgroup ↥(ruP ⊓ Subgroup.centralizer {ruA0}), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5 :=
  sylVerify_sound (N := 256) (a := 8) (m := 455) (by norm_num)
    (by rw [ruCentralizer_a, card_ruL]; norm_num) ⟨227, by norm_num⟩ regIn_ruT ru_cent_checks.2

theorem ru_card_le_of_2B
    (B : Subgroup (Equiv.Perm (Fin 4060))) (hBP : B ≤ ruP)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hx : g * ruA0 * g⁻¹ ∈ B) :
    Nat.card B ≤ 2 ^ 5 := by
  set H : Subgroup (Equiv.Perm (Fin 4060)) := ruP ⊓ Subgroup.centralizer {ruA0} with hH
  set B' : Subgroup (Equiv.Perm (Fin 4060)) := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hB'mem : ∀ y, y ∈ B' ↔ ∃ u ∈ B, y = g⁻¹ * u * g := by
    intro y
    simp only [hB', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩⟩
  have hB'H : B' ≤ H := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (hB'mem y).1 hy
    refine ⟨ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg) (hBP hu)) hg,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g⁻¹ * u * g * ruA0 = g⁻¹ * (u * (g * ruA0 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * ruA0 * g⁻¹) * u) * g := by rw [hcomm u hu _ hx]
      _ = ruA0 * (g⁻¹ * u * g) := by group
  have hcard : Nat.card (B'.subgroupOf H) = Nat.card B := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'H).toEquiv, hB',
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hmem : ∀ x : ↥H, x ∈ B'.subgroupOf H → ∃ u ∈ B, (x : Equiv.Perm (Fin 4060)) =
      g⁻¹ * u * g := fun x hx => (hB'mem _).1 (Subgroup.mem_subgroupOf.1 hx)
  rw [← hcard]
  refine ru_cent_rank (B'.subgroupOf H) (fun x hx y hy => Subtype.ext ?_) fun x hx =>
    Subtype.ext ?_
  · obtain ⟨u, hu, hxu⟩ := hmem x hx
    obtain ⟨v, hv, hyv⟩ := hmem y hy
    simp only [Subgroup.coe_mul, hxu, hyv]
    calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
      _ = g⁻¹ * (v * u) * g := by rw [hcomm u hu v hv]
      _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group
  · obtain ⟨u, hu, hxu⟩ := hmem x hx
    simp only [Subgroup.coe_mul, Subgroup.coe_one, hxu]
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hsq u hu]; group

end CFSG.Quasithin.B45Exc.Ru
