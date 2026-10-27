module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section SecAction

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

@[expose] def d321f_secRho (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) :
    ↥L →* ↥(stabSub (Z.subgroupOf U)) :=
  ((resHom U).comp (Subgroup.inclusion hLU)).codRestrict (stabSub (Z.subgroupOf U))
    fun g => autSub_le_stabSub_subgroupOf hLZ (mem_autSub.2 ⟨⟨g, hLU g.2⟩, g.2, rfl⟩)

@[expose] def d321f_secHom (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) :
    ↥L →* MulAut (Sec U Z) :=
  (quotHom (Z.subgroupOf U)).comp (d321f_secRho hLU hLZ)

theorem d321f_secHom_mk (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (l : ↥L) (w : ↥U) :
    d321f_secHom hLU hLZ l (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨(l : MulAut W) (w : W), (hLU l.2 (w : W)).2 w.2⟩ :=
  rfl

theorem d321f_mem_ker_secHom (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (l : ↥L) :
    l ∈ (d321f_secHom hLU hLZ).ker ↔ (l : MulAut W) ∈ centSec U Z := by
  rw [MonoidHom.mem_ker, mem_centSec]
  constructor
  · intro h
    refine ⟨hLU l.2, fun w hw => ?_⟩
    have := congrArg (fun φ : MulAut (Sec U Z) => φ (QuotientGroup.mk ⟨w, hw⟩)) h
    simp only [d321f_secHom_mk, MulAut.one_apply] at this
    have h2 := (mk_eq_mk_iff (U := Z.subgroupOf U) _ _).1 this
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · rintro ⟨-, h⟩
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [d321f_secHom_mk]
      refine (mk_eq_mk_iff (U := Z.subgroupOf U) _ _).2 ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using h w w.2

theorem d321f_secHom_injective (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hf : L ⊓ centSec U Z = ⊥) : Function.Injective (d321f_secHom hLU hLZ) := by
  refine (MonoidHom.ker_eq_bot_iff _).1 (eq_bot_iff.2 fun g hg => ?_)
  rw [d321f_mem_ker_secHom] at hg
  have hg' : (g : MulAut W) ∈ L ⊓ centSec U Z := ⟨g.2, hg⟩
  rw [hf, Subgroup.mem_bot] at hg'
  exact Subgroup.mem_bot.2 (Subtype.ext hg')

theorem d321f_range_secHom (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) :
    (d321f_secHom hLU hLZ).range = autSec L U Z := by
  ext φ
  rw [MonoidHom.mem_range, autSec, mem_autQuot]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨d321f_secRho hLU hLZ l, mem_autSub.2 ⟨⟨l, hLU l.2⟩, l.2, rfl⟩, rfl⟩
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨g₀, hg₀, hg₀'⟩ := mem_autSub.1 hg'
    refine ⟨⟨(g₀ : MulAut W), hg₀⟩, ?_⟩
    have hρ : d321f_secRho hLU hLZ ⟨(g₀ : MulAut W), hg₀⟩ = g' := Subtype.ext hg₀'
    exact congrArg (quotHom (Z.subgroupOf U)) hρ

@[expose] noncomputable def d321f_autSecEquiv (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hf : L ⊓ centSec U Z = ⊥) : ↥L ≃* ↥(autSec L U Z) :=
  (MonoidHom.ofInjective (d321f_secHom_injective hLU hLZ hf)).trans
    (MulEquiv.subgroupCongr (d321f_range_secHom hLU hLZ))

theorem d321f_autSecEquiv_apply_mk (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hf : L ⊓ centSec U Z = ⊥) (l : ↥L) (u : W) (hu : u ∈ U) :
    ((d321f_autSecEquiv hLU hLZ hf l : ↥(autSec L U Z)) : MulAut (Sec U Z))
        (QuotientGroup.mk ⟨u, hu⟩) =
      QuotientGroup.mk ⟨(l : MulAut W) u, (hLU l.2 u).2 hu⟩ :=
  rfl

end SecAction

section SecPre

variable {W : Type} [CommGroup W] {U Z : Subgroup W}

@[expose] def d321f_secPre (U Z : Subgroup W) (S : Subgroup (Sec U Z)) : Subgroup W :=
  (S.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype

theorem d321f_mem_secPre {S : Subgroup (Sec U Z)} {u : W} :
    u ∈ d321f_secPre U Z S ↔ ∃ hu : u ∈ U, (QuotientGroup.mk ⟨u, hu⟩ : Sec U Z) ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, h, rfl⟩

theorem d321f_secPre_le (S : Subgroup (Sec U Z)) : d321f_secPre U Z S ≤ U :=
  Subgroup.map_subtype_le _

theorem d321f_le_secPre (hZU : Z ≤ U) (S : Subgroup (Sec U Z)) : Z ≤ d321f_secPre U Z S := by
  intro z hz
  have h1 : (QuotientGroup.mk ⟨z, hZU hz⟩ : Sec U Z) = 1 := (QuotientGroup.eq_one_iff _).2 hz
  exact d321f_mem_secPre.2 ⟨hZU hz, by rw [h1]; exact S.one_mem⟩

@[expose] def d321f_secPreHom (S : Subgroup (Sec U Z)) : ↥(d321f_secPre U Z S) →* ↥S where
  toFun u := ⟨QuotientGroup.mk ⟨(u : W), (d321f_mem_secPre.1 u.2).fst⟩,
    (d321f_mem_secPre.1 u.2).snd⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem d321f_secPreHom_surjective (S : Subgroup (Sec U Z)) :
    Function.Surjective (d321f_secPreHom S) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨(x : W), d321f_mem_secPre.2 ⟨x.2, hy⟩⟩, rfl⟩

theorem d321f_secPreHom_coe_eq_one_iff (S : Subgroup (Sec U Z)) (u : ↥(d321f_secPre U Z S)) :
    ((d321f_secPreHom S u : ↥S) : Sec U Z) = 1 ↔ (u : W) ∈ Z :=
  QuotientGroup.eq_one_iff (N := Z.subgroupOf U) ⟨(u : W), (d321f_mem_secPre.1 u.2).fst⟩

theorem d321f_map_mk_subgroupOf (U Z : Subgroup W) :
    (Z.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = ⊥ :=
  (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge

theorem d321f_secPre_inf_sup {k : ℕ} (hZU : Z ≤ U) (S : Fin k → Subgroup (Sec U Z)) (i : Fin k)
    (hind : S i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), S j) = ⊥) :
    d321f_secPre U Z (S i) ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), d321f_secPre U Z (S j)) = Z := by
  have hqs : Function.Surjective (QuotientGroup.mk' (Z.subgroupOf U)) :=
    QuotientGroup.mk'_surjective _
  have hK : (Z.subgroupOf U).map U.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZU
  have hsup : Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), d321f_secPre U Z (S j) =
      (Z.subgroupOf U ⊔ ⨆ (j : Fin k) (_ : j ≠ i),
        (S j).comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype := by
    simp only [d321f_secPre, Subgroup.map_sup, Subgroup.map_iSup, hK]
  have himg : (Z.subgroupOf U ⊔ ⨆ (j : Fin k) (_ : j ≠ i),
        (S j).comap (QuotientGroup.mk' (Z.subgroupOf U))).map (QuotientGroup.mk' (Z.subgroupOf U)) =
      ⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), S j := by
    simp only [Subgroup.map_sup, Subgroup.map_iSup,
      Subgroup.map_comap_eq_self_of_surjective hqs, d321f_map_mk_subgroupOf]
  refine le_antisymm ?_ (le_inf (d321f_le_secPre hZU _) le_sup_left)
  rintro x ⟨hx1, hx2⟩
  rw [hsup] at hx2
  obtain ⟨y, hy, rfl⟩ := hx2
  obtain ⟨hxU, hxS⟩ := d321f_mem_secPre.1 hx1
  have h1 : QuotientGroup.mk' (Z.subgroupOf U) y ∈
      S i ⊓ (⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), S j) := by
    refine ⟨hxS, ?_⟩
    rw [← himg]
    exact ⟨y, hy, rfl⟩
  rw [hind, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem d321f_secPre_sup_eq {k : ℕ} (hZU : Z ≤ U) (S : Fin k → Subgroup (Sec U Z))
    (hsum : (⊥ ⊔ ⨆ i, S i) = ⊤) : (Z ⊔ ⨆ i, d321f_secPre U Z (S i)) = U := by
  have hqs : Function.Surjective (QuotientGroup.mk' (Z.subgroupOf U)) :=
    QuotientGroup.mk'_surjective _
  have hK : (Z.subgroupOf U).map U.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZU
  refine le_antisymm (sup_le hZU (iSup_le fun i => d321f_secPre_le _)) fun x hx => ?_
  have hsup : (Z ⊔ ⨆ i, d321f_secPre U Z (S i)) =
      (Z.subgroupOf U ⊔ ⨆ i, (S i).comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype := by
    simp only [d321f_secPre, Subgroup.map_sup, Subgroup.map_iSup, hK]
  have himg : (Z.subgroupOf U ⊔ ⨆ i, (S i).comap (QuotientGroup.mk' (Z.subgroupOf U))).map
      (QuotientGroup.mk' (Z.subgroupOf U)) = ⊤ := by
    simp only [Subgroup.map_sup, Subgroup.map_iSup,
      Subgroup.map_comap_eq_self_of_surjective hqs, d321f_map_mk_subgroupOf]
    exact hsum
  have hy : (⟨x, hx⟩ : ↥U) ∈
      Z.subgroupOf U ⊔ ⨆ i, (S i).comap (QuotientGroup.mk' (Z.subgroupOf U)) := by
    have h1 : QuotientGroup.mk' (Z.subgroupOf U) ⟨x, hx⟩ ∈
        (Z.subgroupOf U ⊔ ⨆ i, (S i).comap (QuotientGroup.mk' (Z.subgroupOf U))).map
          (QuotientGroup.mk' (Z.subgroupOf U)) := by
      rw [himg]
      trivial
    obtain ⟨t, ht, hty⟩ := h1
    have h2 : (⟨x, hx⟩ : ↥U) * t⁻¹ ∈ Z.subgroupOf U := by
      rw [← QuotientGroup.ker_mk' (Z.subgroupOf U), MonoidHom.mem_ker, map_mul, map_inv, hty,
        mul_inv_cancel]
    rw [← inv_mul_cancel_right (⟨x, hx⟩ : ↥U) t]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2) ht
  rw [hsup]
  exact ⟨⟨x, hx⟩, hy, rfl⟩

end SecPre

section Transport

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem d321f_realizesVia_secPre_of_equiv (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hZU : Z ≤ U) (e : ↥L ≃* ↥(autSec L U Z))
    (he : ∀ (l : ↥L) (u : W) (hu : u ∈ U),
      ((e l : ↥(autSec L U Z)) : MulAut (Sec U Z)) (QuotientGroup.mk ⟨u, hu⟩) =
        QuotientGroup.mk ⟨(l : MulAut W) u, (hLU l.2 u).2 hu⟩)
    {D : FFModel} {S : Subgroup (Sec U Z)} {ρ : D.Gam →* ↥(autSec L U Z)}
    (h : D.RealizesVia (autSec L U Z) S ⊥ ρ) :
    D.RealizesVia L (d321f_secPre U Z S) Z (e.symm.toMonoidHom.comp ρ) := by
  obtain ⟨hsurj, -, hkerle, hinv, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  refine ⟨e.symm.surjective.comp hsurj, d321f_le_secPre hZU S, hkerle, ?_,
    fun g z hz => (hLZ g.2 z).2 hz, hsec, hkerinv, β.comp (d321f_secPreHom S),
    hβs.comp (d321f_secPreHom_surjective S), ?_, ?_⟩
  · intro g u hu
    obtain ⟨huU, hmk⟩ := d321f_mem_secPre.1 hu
    refine d321f_mem_secPre.2 ⟨(hLU g.2 u).2 huU, ?_⟩
    have h1 := hinv (e g) _ hmk
    rwa [he g u huU] at h1
  · intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot]
    exact d321f_secPreHom_coe_eq_one_iff S u
  · intro γ u m hu hm hum
    obtain ⟨huU, -⟩ := d321f_mem_secPre.1 u.2
    have hρ := he (e.symm (ρ γ)) (u : W) huU
    rw [MulEquiv.apply_symm_apply] at hρ
    have hru : ((ρ γ : ↥(autSec L U Z)) : MulAut (Sec U Z)) (d321f_secPreHom S u : Sec U Z) ∈ S :=
      hinv (ρ γ) _ (d321f_secPreHom S u).2
    have key := hβe γ (d321f_secPreHom S u) m hru hm hum
    have hr : d321f_secPreHom S ⟨((e.symm (ρ γ) : ↥L) : MulAut W) (u : W), hu⟩ =
        ⟨((ρ γ : ↥(autSec L U Z)) : MulAut (Sec U Z)) (d321f_secPreHom S u : Sec U Z), hru⟩ :=
      Subtype.ext hρ.symm
    show β (d321f_secPreHom S ⟨((e.symm (ρ γ) : ↥L) : MulAut W) (u : W), hu⟩) = _
    rw [hr]
    exact key

theorem d321f_realizesVia_secPre (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hZU : Z ≤ U)
    (hf : L ⊓ centSec U Z = ⊥) {D : FFModel} {S : Subgroup (Sec U Z)}
    {ρ : D.Gam →* ↥(autSec L U Z)} (h : D.RealizesVia (autSec L U Z) S ⊥ ρ) :
    D.RealizesVia L (d321f_secPre U Z S) Z
      ((d321f_autSecEquiv hLU hLZ hf).symm.toMonoidHom.comp ρ) :=
  d321f_realizesVia_secPre_of_equiv hLU hLZ hZU (d321f_autSecEquiv hLU hLZ hf)
    (d321f_autSecEquiv_apply_mk hLU hLZ hf) h

theorem d321f_directSum_of_autSec (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hZU : Z ≤ U)
    (hf : L ⊓ centSec U Z = ⊥) {D : FFModel} {k : ℕ}
    (h : DirectSumOfCopies (autSec L U Z) (⊤ : Subgroup (Sec U Z)) ⊥ D k) :
    DirectSumOfCopies L U Z D k := by
  obtain ⟨S, ρ, -, hind, hsum, hreal⟩ := h
  exact ⟨fun i => d321f_secPre U Z (S i), (d321f_autSecEquiv hLU hLZ hf).symm.toMonoidHom.comp ρ,
    fun i => d321f_le_secPre hZU _, fun i => d321f_secPre_inf_sup hZU S i (hind i),
    d321f_secPre_sup_eq hZU S hsum, fun i => d321f_realizesVia_secPre hLU hLZ hZU hf (hreal i)⟩

theorem d321f_isPSL_of_autSec {n p e : ℕ} (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hf : L ⊓ centSec U Z = ⊥) (h : IsPSL n p e ↥(autSec L U Z)) : IsPSL n p e ↥L :=
  isPSL_congr (d321f_autSecEquiv hLU hLZ hf).symm h

end Transport

end CFSG.Quasithin
