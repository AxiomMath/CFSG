module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreB
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLaMain

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {R Rp H K Q LH V : Subgroup G} {F : Type} [Field F] [Fintype F]
  {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

private theorem conj_comm_coreC {s z b a : G} (ha : a = ⁅z, s⁆) (hsa : s * a = a * s)
    (hba : b * a = a * b) (hbz : b * z = z * b) : s * b * s⁻¹ * z = z * (s * b * s⁻¹) := by
  have key0 : a * s * z = z * s := by
    rw [ha, commutatorElement_def]; group
  have key1 : s * a * z = z * s := by rw [hsa]; exact key0
  have hinv : s⁻¹ * z = a * z * s⁻¹ := by
    calc s⁻¹ * z = s⁻¹ * (z * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * a * z) * s⁻¹ := by rw [key1]
      _ = a * z * s⁻¹ := by group
  calc s * b * s⁻¹ * z = s * b * (s⁻¹ * z) := by group
    _ = s * b * (a * z * s⁻¹) := by rw [hinv]
    _ = s * (b * a) * z * s⁻¹ := by group
    _ = s * (a * b) * z * s⁻¹ := by rw [hba]
    _ = (s * a) * (b * z) * s⁻¹ := by group
    _ = (s * a) * (z * b) * s⁻¹ := by rw [hbz]
    _ = (s * a * z) * b * s⁻¹ := by group
    _ = (z * s) * b * s⁻¹ := by rw [key1]
    _ = z * (s * b * s⁻¹) := by group

private theorem conj_comm_sub_coreC {s a b : G} (hsa : s * a = a * s) (hba : b * a = a * b) :
    s * b * s⁻¹ * a = a * (s * b * s⁻¹) := by
  have hinv : s⁻¹ * a = a * s⁻¹ := by
    calc s⁻¹ * a = s⁻¹ * (a * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * a) * s⁻¹ := by rw [hsa]
      _ = a * s⁻¹ := by group
  calc s * b * s⁻¹ * a = s * b * (s⁻¹ * a) := by group
    _ = s * b * (a * s⁻¹) := by rw [hinv]
    _ = s * (b * a) * s⁻¹ := by group
    _ = s * (a * b) * s⁻¹ := by rw [hba]
    _ = (s * a) * b * s⁻¹ := by group
    _ = (a * s) * b * s⁻¹ := by rw [hsa]
    _ = a * (s * b * s⁻¹) := by group

private theorem mem_normalizer_perfectCore_coreC (h : CoreHyp R Rp H K Q LH V F α β)
    (hZC : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) {s : G}
    (hsV : ∀ v ∈ V, s * v = v * s) {A : Subgroup G} (hAV : A ≤ V)
    (hZA : ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G), ⁅z', s⁆ ∈ A)
    (hρ : ∃ ρ : ↥(perfectCore (K ⊓ Subgroup.centralizer (A : Set G))) →* ↥(StatedSL 2 F),
      Function.Surjective ρ ∧ IsPGroup 2 ρ.ker) :
    s ∈ Subgroup.normalizer ((perfectCore (K ⊓ Subgroup.centralizer (A : Set G)) : Subgroup G) :
      Set G) := by
  set B := perfectCore (K ⊓ Subgroup.centralizer (A : Set G)) with hBdef
  obtain ⟨ρ, hρs, hρk⟩ := hρ
  have hBle : B ≤ K ⊓ Subgroup.centralizer (A : Set G) := perfectCore_le _
  have hBK : B ≤ K := hBle.trans inf_le_left
  have hBperf : ⁅B, B⁆ = B := perfectCore_perfect _
  have hBA : ∀ b ∈ B, ∀ a ∈ A, a * b = b * a := fun b hb a ha =>
    Subgroup.mem_centralizer_iff.mp (hBle hb).2 a ha
  have hBZ : ∀ b ∈ B, ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
      b * z' = z' * b := fun b hb z' hz' =>
    Subgroup.mem_centralizer_iff.mp hz'.2 b (hBK hb)
  have hsA : ∀ a ∈ A, s * a = a * s := fun a ha => hsV a (hAV ha)
  set f : G →* G := (MulAut.conj s).toMonoidHom with hfdef
  have hf_apply : ∀ x, f x = s * x * s⁻¹ := fun x => rfl
  have hf_inj : Function.Injective f := (MulAut.conj s).injective
  set B' := B.map f with hB'def
  have hB'perf : ⁅B', B'⁆ = B' := by
    rw [hB'def, ← Subgroup.map_commutator, hBperf]
  have hB'cent : ∀ g ∈ B', ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
      z' * g = g * z' := by
    intro g hg z' hz'
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
    rw [hf_apply]
    exact (conj_comm_coreC (a := ⁅z', s⁆) (z := z') (b := b) rfl (hsA _ (hZA z' hz'))
      (hBA b hb _ (hZA z' hz')).symm (hBZ b hb z' hz')).symm
  have hB'centA : ∀ g ∈ B', ∀ a ∈ A, a * g = g * a := by
    intro g hg a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
    rw [hf_apply]
    exact (conj_comm_sub_coreC (hsA a ha) (hBA b hb a ha).symm).symm
  have hB'H : B' ≤ H := fun g hg =>
    (h.NZ hZC) (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (hB'cent g hg)))
  obtain ⟨g, hgs, hgi⟩ : ∃ g : ↥B' →* ↥B, Function.Surjective g ∧ Function.Injective g :=
    ⟨(Subgroup.equivMapOfInjective B f hf_inj).symm.toMonoidHom,
      (Subgroup.equivMapOfInjective B f hf_inj).symm.surjective,
      (Subgroup.equivMapOfInjective B f hf_inj).symm.injective⟩
  have hB'ρ : ∃ ρ' : ↥B' →* ↥(StatedSL 2 F), Function.Surjective ρ' ∧ IsPGroup 2 ρ'.ker := by
    refine ⟨ρ.comp g, hρs.comp hgs, ?_⟩
    have hker : (ρ.comp g).ker = ρ.ker.comap g := by
      ext x
      rfl
    rw [hker]
    exact hρk.comap_of_injective g hgi
  have hB'K : B' ≤ K := h.h27 B' hB'H hB'perf hB'ρ
  have hB'B : B' ≤ B :=
    le_perfectCore_of_perfect (le_inf hB'K (fun g hg => Subgroup.mem_centralizer_iff.mpr
      (hB'centA g hg))) hB'perf
  have hcard : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective hf_inj
  have hBeq : B' = B := Subgroup.eq_of_le_of_card_ge hB'B hcard.symm.le
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hfx : f x ∈ B' := Subgroup.mem_map_of_mem f hx
    rw [hBeq] at hfx
    exact hfx
  · intro hx
    have hfx : f x ∈ B' := by
      rw [hBeq]
      exact hx
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hfx
    rw [← hf_inj hfy]
    exact hy

theorem false_of_good (h : CoreHyp R Rp H K Q LH V F α β)
    (hZC : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) {s' t z : G}
    (hs' : InR2 R Rp V s') (ht : t ∈ LH) (ht2 : t * t ∈ R)
    (hz : z ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G)) (hzs : ⁅z, s'⁆ ≠ 1)
    (hgood : ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
      ∃ q ∈ V, ⁅z', s'⁆ = ⁅t, q⁆) : False := by
  set S : Set G := {a | ∃ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
    a = ⁅z', s'⁆} with hSdef
  have hSV : ∀ a ∈ S, a ∈ V := by
    rintro a ⟨z', hz', rfl⟩
    exact hs'.2.2 z' hz'.1
  have hAV : Subgroup.closure S ≤ V := (Subgroup.closure_le V).mpr hSV
  have hS : ∀ a ∈ S, ∃ q ∈ V, a = ⁅t, q⁆ := by
    rintro a ⟨z', hz', rfl⟩
    exact hgood z' hz'
  have hSne : ∃ a ∈ S, a ≠ 1 := ⟨⁅z, s'⁆, ⟨z, hz, rfl⟩, hzs⟩
  have htV : ∀ q ∈ V, t * q * t⁻¹ ∈ V := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (h.LHV ht) q).mp hq
  have htt : t * t ∈ Subgroup.centralizer (V : Set G) := h.VRp (h.RRp ht2)
  have ht2V : ∀ q ∈ V, t * t * q = q * (t * t) := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp htt q hq).symm
  obtain ⟨⟨ρ, hρs, hρk⟩, hVB⟩ :=
    laMain h.co h.αsurj h.αker h.F2 h.VS (h.LHK ht) htV ht2V S hS hSne
  have hsV : ∀ v ∈ V, s' * v = v * s' := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (h.VRp hs'.1) v hv).symm
  have hZA : ∀ z' ∈ omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G),
      ⁅z', s'⁆ ∈ Subgroup.closure S := fun z' hz' =>
    Subgroup.subset_closure ⟨z', hz', rfl⟩
  have hBn := mem_normalizer_perfectCore_coreC h hZC hsV hAV hZA ⟨ρ, hρs, hρk⟩
  have hΩn : s' ∈ Subgroup.normalizer (omegaOneCenterOf R : Set G) :=
    A4.normalizer_le_normalizer_omegaOneCenterOf R hs'.2.1
  have hcomm := CFSG.Quasithin.A4.mem_normalizer_commutator hΩn hBn
  set B := perfectCore (K ⊓ Subgroup.centralizer ((Subgroup.closure S : Subgroup G) : Set G))
    with hBdef
  have hBK : B ≤ K := (perfectCore_le _).trans inf_le_left
  have hQeq : ⁅omegaOneCenterOf R, B⁆ = Q := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono le_rfl hBK).trans h.ΩK
    · rw [← hVB]
      exact Subgroup.commutator_mono h.VΩ le_rfl
  rw [hQeq] at hcomm
  have hsH : s' ∈ H := h.NQ hcomm
  have hsR : s' ∈ R := h.RpH (Subgroup.mem_inf.mpr ⟨hs'.1, hsH⟩)
  exact hzs (commutatorElement_eq_one_iff_mul_comm.mpr (omega_comm_R hz.1 hsR))

theorem centk_core (h : CoreHyp R Rp H K Q LH V F α β) :
    omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  by_contra hZC
  have hRlt : R < Rp := lt_of_le_of_ne h.RRp fun e => hZC (h.RZ e)
  obtain ⟨s', t, z, hs', ht, ht2, hz, hzs, hgood⟩ := exists_good h hZC hRlt
  exact false_of_good h hZC hs' ht ht2 hz hzs hgood

end CFSG.Quasithin.H13.Ch4.CentK
