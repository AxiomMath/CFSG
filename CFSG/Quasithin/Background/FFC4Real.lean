module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.FFC2Sym
public import CFSG.Quasithin.Background.FFC2G2

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.QuasithinUnique.Bridge.Alt57Model

section Faithful

variable {V : Type*} [CommGroup V]

theorem injective_of_faithful_sec {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) : Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

end Faithful

section Models

theorem symDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.symDn n).Faithful := by
  intro σ h
  by_contra hne
  obtain ⟨m, hm, hmove⟩ := exists_core_move hn hne
  have := h m hm
  exact hmove (Subgroup.mem_inf.1 this).1

theorem altDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.altDn n).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin n))) h
  have h' : (σ : Equiv.Perm (Fin n)) = 1 :=
    symDn_faithful hn (σ : Equiv.Perm (Fin n)) (fun m hm => h m hm)
  exact Subtype.ext h'


theorem a7Four_faithful (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    (FFModel.a7Four α).Faithful := by
  intro (γ : ↥(alternatingGroup (Fin 7))) h
  have h1 : (⟨α (altLift7 γ), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 4)
      (ZMod 2)))) = 1 := by
    refine natAct_faithful (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))) _ ?_
    intro m
    exact Subgroup.mem_bot.1 (h m (Subgroup.mem_top _))
  have h2 : α (altLift7 γ) = 1 := congrArg Subtype.val h1
  have h3 : altLift7 γ = 1 := α.injective (h2.trans (map_one α).symm)
  have h4 : Function.Injective (altLift7 : ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 8))) := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb : Fin 7 ↪ Fin 8) this)
  exact h4 (h3.trans (map_one altLift7).symm)

theorem zornQ_faithful {K : Type} [Field K] [CharP K 2]
    (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) (hΓ : Γ ≤ CFSG.Open.quasithinG2 K) :
    (FFModel.zornQ Γ).Faithful := by
  intro (γ : ↥Γ) h
  have hg : IsZornAuto (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) :=
    mem_quasithinG2_isZornAuto (hΓ γ.2)
  have hO : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 →
      ∃ c : K, (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = x + (c, 0, 0, c) := by
    intro x hx
    have hm0 : Multiplicative.ofAdd x ∈ (FFModel.zornQ Γ).sec := hx
    obtain ⟨c, hc⟩ := h _ hm0
    refine ⟨c, ?_⟩
    have h5 : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x - x = (c, 0, 0, c) := by
      have h6 : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x + -x = (c, 0, 0, c) := hc
      rwa [← sub_eq_add_neg] at h6
    exact sub_eq_iff_eq_add'.1 h5
  have h4 := zornAuto_eq_one hg hO
  exact Subtype.ext (LinearEquiv.ext h4)

end Models

section Transport

theorem RealizesVia.transport {W V : Type*} [CommGroup W] [CommGroup V] (ι : W →* V)
    (hι : Function.Injective ι) {G₂ : Subgroup (MulAut V)} {H : Subgroup (MulAut W)}
    (e : ↥G₂ ≃* ↥H) (he : ∀ (g : ↥G₂) (w : W), ι ((e g : MulAut W) w) = (g : MulAut V) (ι w))
    {D : FFModel} {U Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    D.RealizesVia G₂ (U.map ι) (Z.map ι) (e.symm.toMonoidHom.comp π) := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hact : ∀ (g : ↥G₂) (w : W), (g : MulAut V) (ι w) = ι ((e g : MulAut W) w) :=
    fun g w => (he g w).symm
  refine ⟨?_, Subgroup.map_mono hZU, hkersec, ?_, ?_, hsec, hker, ?_⟩
  · exact e.symm.surjective.comp hsurj
  · rintro g _ ⟨u, hu, rfl⟩
    rw [hact]
    exact ⟨_, hHU (e g) u hu, rfl⟩
  · rintro g _ ⟨z, hz, rfl⟩
    rw [hact]
    exact ⟨_, hHZ (e g) z hz, rfl⟩
  · let iso : ↥(U.map ι) ≃* ↥U := (Subgroup.equivMapOfInjective U ι hι).symm
    have hiso : ∀ (u : ↥(U.map ι)), ι ((iso u : ↥U) : W) = (u : V) := by
      intro u
      have := (Subgroup.equivMapOfInjective U ι hι).apply_symm_apply u
      exact congrArg Subtype.val this
    refine ⟨β.comp iso.toMonoidHom, hβs.comp iso.surjective, ?_, ?_⟩
    · intro u
      show β (iso u) = 1 ↔ _
      rw [hβk, ← hiso u]
      exact (Subgroup.mem_map_iff_mem hι).symm
    · intro γ u m hu hm hbu
      set g : ↥G₂ := e.symm (π γ) with hg
      have hge : e g = π γ := by rw [hg]; exact e.apply_symm_apply _
      set u₀ : ↥U := iso u with hu₀
      have hU' : ((π γ : ↥H) : MulAut W) (u₀ : W) ∈ U := hHU (π γ) u₀ u₀.2
      have h1 : (g : MulAut V) (u : V) = ι (((π γ : ↥H) : MulAut W) (u₀ : W)) := by
        rw [← hiso u, hact, hge]
      have h2 : iso ⟨(g : MulAut V) (u : V), hu⟩ = ⟨((π γ : ↥H) : MulAut W) (u₀ : W), hU'⟩ := by
        apply Subtype.ext
        apply hι
        exact (hiso _).trans h1
      have h3 := hβe γ u₀ m hU' hm hbu
      show β (iso ⟨(g : MulAut V) (u : V), hu⟩) = _
      rw [h2]
      exact h3

end Transport

section Extend

variable {V : Type*} [CommGroup V]

theorem RealizesVia.extend {H : Subgroup (MulAut V)} {D : FFModel} {U Z C : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (hC : ∀ h : ↥H, ∀ c ∈ C, (h : MulAut V) c ∈ C)
    (hUC : U ⊓ C = Z) : D.RealizesVia H (U ⊔ C) C π := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  let f : ↥U × ↥C →* ↥(U ⊔ C) :=
    { toFun := fun p => ⟨(p.1 : V) * (p.2 : V), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show (a.1 : V) * (b.1 : V) * ((a.2 : V) * (b.2 : V)) =
          ((a.1 : V) * (a.2 : V)) * ((b.1 : V) * (b.2 : V))
        exact mul_mul_mul_comm _ _ _ _ }
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  have hker_f : f.ker ≤ (β.comp (MonoidHom.fst ↥U ↥C)).ker := by
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    have hab' : (a : V) * (b : V) = 1 := congrArg Subtype.val hab
    have haC : (a : V) ∈ C := by
      have : (a : V) = ((b : V))⁻¹ := eq_inv_of_mul_eq_one_left hab'
      rw [this]
      exact C.inv_mem b.2
    have haZ : (a : V) ∈ Z := by
      rw [← hUC]
      exact ⟨a.2, haC⟩
    rw [MonoidHom.mem_ker]
    exact (hβk a).2 haZ
  let β' : ↥(U ⊔ C) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.lift f.ker (β.comp (MonoidHom.fst ↥U ↥C)) hker_f).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
  have hβ' : ∀ (a : ↥U) (b : ↥C), β' ⟨(a : V) * (b : V), Subgroup.mul_mem_sup a.2 b.2⟩ = β a := by
    intro a b
    have : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm ⟨(a : V) * (b : V),
        Subgroup.mul_mem_sup a.2 b.2⟩ = (QuotientGroup.mk (a, b) : (↥U × ↥C) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift f.ker (β.comp (MonoidHom.fst ↥U ↥C)) hker_f)
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm ⟨(a : V) * (b : V),
        Subgroup.mul_mem_sup a.2 b.2⟩) = β a
    rw [this, QuotientGroup.lift_mk]
    rfl
  refine ⟨hsurj, le_sup_right, hkersec, ?_, hC, hsec, hker, β', ?_, ?_, ?_⟩
  · intro h x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hHU h y hy) (hC h z hz)
  · intro m
    obtain ⟨a, ha⟩ := hβs m
    exact ⟨⟨(a : V) * 1, Subgroup.mul_mem_sup a.2 C.one_mem⟩, by
      have := hβ' a 1
      simpa using this.trans ha⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    have h1 := hβ' ⟨y, hy⟩ ⟨z, hz⟩
    show β' ⟨y * z, hx⟩ = 1 ↔ y * z ∈ C
    rw [h1]
    constructor
    · intro hb
      have hyZ : y ∈ Z := (hβk ⟨y, hy⟩).1 hb
      have hyC : y ∈ C := by rw [← hUC] at hyZ; exact hyZ.2
      exact C.mul_mem hyC hz
    · intro hyz
      have hyC : y ∈ C := by
        have : y = (y * z) * z⁻¹ := by group
        rw [this]
        exact C.mul_mem hyz (C.inv_mem hz)
      have hyZ : y ∈ Z := by rw [← hUC]; exact ⟨hy, hyC⟩
      exact (hβk ⟨y, hy⟩).2 hyZ
  · intro γ x m hxu hm hbx
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 x.2
    have hx' : x = ⟨y * z, Subgroup.mul_mem_sup hy hz⟩ := Subtype.ext hyz.symm
    have hbx' : β ⟨y, hy⟩ = QuotientGroup.mk m := by
      rw [hx', hβ' ⟨y, hy⟩ ⟨z, hz⟩] at hbx
      exact hbx
    have hHy : ((π γ : ↥H) : MulAut V) y ∈ U := hHU (π γ) y hy
    have hHz : ((π γ : ↥H) : MulAut V) z ∈ C := hC (π γ) z hz
    have h1 := hβe γ ⟨y, hy⟩ m hHy hm hbx'
    have h2 : (⟨((π γ : ↥H) : MulAut V) (x : V), hxu⟩ : ↥(U ⊔ C)) =
        ⟨((π γ : ↥H) : MulAut V) y * ((π γ : ↥H) : MulAut V) z, Subgroup.mul_mem_sup hHy hHz⟩ := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (x : V) = _
      rw [← hyz, map_mul]
    rw [h2, hβ' ⟨_, hHy⟩ ⟨_, hHz⟩]
    exact h1

end Extend


end FFC

end CFSG.Quasithin
