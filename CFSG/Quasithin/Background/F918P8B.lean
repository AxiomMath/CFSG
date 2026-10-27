module

public import CFSG.Quasithin.Background.F918N2
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

section Bridge

private theorem p8b_exists_equiv {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂]
    (f₁ : G →* G₁) (f₂ : G →* G₂) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (hk : ∀ g, f₁ g = 1 ↔ f₂ g = 1) : ∃ φ : G₁ ≃* G₂, ∀ g, φ (f₁ g) = f₂ g := by
  have hker : f₁.ker = f₂.ker := by
    ext g
    simpa only [MonoidHom.mem_ker] using hk g
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ h₂)), fun g => ?_⟩
  have e1 : (QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).symm (f₁ g) =
      QuotientGroup.mk g := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1]
  rfl

variable {W : Type} [CommGroup W]

theorem p8b_iso_of_secIsoL {L : Subgroup (MulAut W)} {C I I' : Subgroup W}
    [MulDistribMulAction ↥L (W ⧸ C)]
    (hact : ∀ (a : ↥L) (q : W),
      a • (QuotientGroup.mk q : W ⧸ C) = QuotientGroup.mk ((a : MulAut W) q))
    (h : SecIsoL L I (I ⊓ C) I' (I' ⊓ C)) :
    XMod.Iso ↥L (I.map (QuotientGroup.mk' C)) (I'.map (QuotientGroup.mk' C)) := by
  obtain ⟨-, -, hIinv, -, hI'inv, -, β, hβs, hβk, hβe⟩ := B5.secIsoL_iff.1 h
  set ψ : ↥I →* ↥(I.map (QuotientGroup.mk' C)) := (QuotientGroup.mk' C).subgroupMap I
  set ψ' : ↥I' →* ↥(I'.map (QuotientGroup.mk' C)) := (QuotientGroup.mk' C).subgroupMap I'
  have hψ : Function.Surjective ψ := MonoidHom.subgroupMap_surjective _ _
  have hψ' : Function.Surjective ψ' := MonoidHom.subgroupMap_surjective _ _
  have hψc : ∀ u : ↥I, ((ψ u : ↥(I.map (QuotientGroup.mk' C))) : W ⧸ C) =
      QuotientGroup.mk (u : W) := fun u => rfl
  have hψ'c : ∀ m : ↥I', ((ψ' m : ↥(I'.map (QuotientGroup.mk' C))) : W ⧸ C) =
      QuotientGroup.mk (m : W) := fun m => rfl
  have hψk : ∀ u : ↥I, ψ u = 1 ↔ (u : W) ∈ C := by
    intro u
    rw [Subtype.ext_iff, hψc, Subgroup.coe_one, QuotientGroup.eq_one_iff]
  have hψ'k : ∀ m : ↥I', ψ' m = 1 ↔ (m : W) ∈ C := by
    intro m
    rw [Subtype.ext_iff, hψ'c, Subgroup.coe_one, QuotientGroup.eq_one_iff]
  have hker' : (I' ⊓ C).subgroupOf I' ≤ ψ'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ'k]
    exact (Subgroup.mem_subgroupOf.1 hx).2
  set ψb : ↥I' ⧸ (I' ⊓ C).subgroupOf I' →* ↥(I'.map (QuotientGroup.mk' C)) :=
    QuotientGroup.lift _ ψ' hker'
  have hψb_mk : ∀ m : ↥I', ψb (QuotientGroup.mk m) = ψ' m := fun m => rfl
  set θ : ↥I →* ↥(I'.map (QuotientGroup.mk' C)) := ψb.comp β
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨m, rfl⟩ := hψ' y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    refine ⟨u, ?_⟩
    change ψb (β u) = ψ' m
    rw [hu, hψb_mk]
  have hθm : ∀ (u : ↥I) (m : ↥I'), β u = QuotientGroup.mk m → θ u = ψ' m := by
    intro u m hum
    change ψb (β u) = ψ' m
    rw [hum, hψb_mk]
  have hθk : ∀ u : ↥I, ψ u = 1 ↔ θ u = 1 := by
    intro u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    rw [hθm u m hm.symm, hψk, hψ'k]
    have h1 : (m : W) ∈ C ↔ β u = 1 := by
      rw [← hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hc => ⟨m.2, hc⟩, fun hc => hc.2⟩
    have h2 : β u = 1 ↔ (u : W) ∈ C := by
      rw [hβk u, Subgroup.mem_inf]
      exact ⟨fun hc => hc.2, fun hc => ⟨u.2, hc⟩⟩
    rw [h1, h2]
  obtain ⟨φ, hφ⟩ := p8b_exists_equiv ψ θ hψ hθs hθk
  refine ⟨φ, fun a l l' hll' => ?_⟩
  obtain ⟨u, rfl⟩ := hψ l
  obtain ⟨u', rfl⟩ := hψ l'
  rw [hφ, hφ]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β u')
  rw [hθm u m hm.symm, hθm u' m' hm'.symm, hψ'c, hψ'c, hact]
  rw [hψc, hψc, hact] at hll'
  have hau : (a : MulAut W) (u : W) ∈ I := hIinv a (u : W) u.2
  have hmem : ((a : MulAut W) (u : W))⁻¹ * (u' : W) ∈ I ⊓ C := by
    refine ⟨I.mul_mem (I.inv_mem hau) u'.2, ?_⟩
    exact QuotientGroup.eq.1 hll'
  have hβ1 : β ⟨(a : MulAut W) (u : W), hau⟩ = β u' := by
    have h1 : β ((⟨(a : MulAut W) (u : W), hau⟩ : ↥I)⁻¹ * u') = 1 := (hβk _).2 hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have ham : (a : MulAut W) (m : W) ∈ I' := hI'inv a (m : W) m.2
  have hβ2 := hβe a u m hau ham hm.symm
  rw [hβ1, ← hm'] at hβ2
  have hβ3 := QuotientGroup.eq.1 hβ2.symm
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hβ3
  exact QuotientGroup.eq.2 hβ3.2

theorem p8b_iso_tilde_of_secIsoL {L : Subgroup (MulAut W)} {U I I' : Subgroup W} (hI : I ≤ U)
    (hI' : I' ≤ U) (h : SecIsoL L I (I ⊓ fixV L) I' (I' ⊓ fixV L)) :
    XMod.Iso ↥L (tilde L U I) (tilde L U I') := by
  have e : ∀ J : Subgroup W, J ≤ U → J ⊓ modFix L U = J ⊓ fixV L := by
    intro J hJ
    rw [n2_modFix_eq, ← inf_assoc, inf_eq_left.2 hJ]
  refine p8b_iso_of_secIsoL (C := modFix L U) (fun a q => rfl) ?_
  rw [e I hI, e I' hI']
  exact h

end Bridge

theorem d310_not_secIsoL {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} (hD : D3Std M Mp T L V) {t : MulAut W} (ht : t ∈ T)
    (hsum : IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t.toMonoidHom) (orbSup T V)) :
    ¬ SecIsoL Mp V (V ⊓ fixV Mp) (V.map t.toMonoidHom) (V.map t.toMonoidHom ⊓ fixV Mp) := by
  intro hiso
  have hTX : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    rw [hD.hyp.Mp_eq]
    exact le_normalizer_conjClosure L T
  have hW : ∀ t ∈ T, ∀ w ∈ orbSup T V, t • w ∈ orbSup T V :=
    fun _ ht _ hw => mem_orbSup_of_mem_map ht hw
  have hbridge : XMod.Iso ↥Mp (tilde Mp (orbSup T V) V)
      (tilde Mp (orbSup T V) (V.map t.toMonoidHom)) :=
    p8b_iso_tilde_of_secIsoL (le_orbSup T V) (map_le_orbSup ht) hiso
  have heq : tilde Mp (orbSup T V) V = tilde Mp (orbSup T V) (V.map t.toMonoidHom) := by
    have h := tilde_smul_eq_of_iso_of_mem_irrPlusOn hTX hW hD.irrT (t := 1) (r := t) T.one_mem ht
      (by rw [one_smul]; exact hbridge)
    rw [one_smul] at h
    exact h
  have hsup : V ⊔ modFix Mp (orbSup T V) = V.map t.toMonoidHom ⊔ modFix Mp (orbSup T V) := by
    rw [← comap_tilde, ← comap_tilde, heq]
  have hVfix : V ≤ fixV Mp := by
    intro v hv
    have h1 : v ∈ V ⊔ modFix Mp (orbSup T V) := Subgroup.mem_sup_left hv
    have h2 : v ∈ V.map t.toMonoidHom ⊔ modFix Mp (orbSup T V) := hsup ▸ h1
    rw [n2_modFix_eq] at h1 h2
    exact (hsum.2 ⟨h1, h2⟩).2
  have hlt : XMod.fixed ↥Mp V < V := hD.hyp.irr.2.2.2.1
  exact lt_irrefl _ (lt_of_lt_of_le hlt fun v hv => ⟨hv, fun a => hVfix hv a a.2⟩)

end CFSG.Quasithin
