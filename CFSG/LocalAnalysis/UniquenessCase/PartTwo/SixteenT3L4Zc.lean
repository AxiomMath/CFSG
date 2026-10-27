module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Stab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_inf_cTilde_isPGroup {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) :
    IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  rw [hY.ker_eq]
  exact CFSG.pCore_isPGroup.map _

theorem s16t_l4_not_dvd_ker {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  obtain ⟨n, hn⟩ := (s16t_l4_inf_cTilde_isPGroup hY).exists_card_eq
  rw [hn]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem s16t_l4_zc_quot (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) :
    ∃ Ψ : ↥(Y ⊓ centralizer ({w} : Set G)) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Close16Quot3 (Y ⊓ centralizer ({w} : Set G)) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) Ψ ∧
        Ψ.ker ≠ ⊥ := by
  have hZM : Y ⊓ centralizer ({w} : Set G) ≤ D.M := inf_le_left.trans hY.le
  obtain ⟨φ, hφs, hφk⟩ := s16t_l4_exists_hom_barSub (hV := hV) (s16t_l4_le_stabTil hS) hZM
  have hbar := s16t_l4_barSub_cent_eq hS hY hw hpt
  obtain ⟨f, hfs, hf2, hf8⟩ := hpt.quot
  let e := MulEquiv.subgroupCongr hbar
  let g : ↥(Y ⊓ centralizer ({w} : Set G)) →* _ := e.toMonoidHom.comp φ
  have hgs : Function.Surjective g := e.surjective.comp hφs
  have hφ2 : IsPGroup 2 ↥φ.ker := by
    rw [hφk]
    refine IsPGroup.of_equiv
      (G := ↥((Y ⊓ centralizer ({w} : Set G)) ⊓ F11.CTilde D.M V₀ V)) ?_
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    exact IsPGroup.to_le (s16t_l4_inf_cTilde_isPGroup hY) (inf_le_inf inf_le_left le_rfl)
  have hg2 : IsPGroup 2 ↥g.ker := by
    have : g.ker = φ.ker := MonoidHom.ker_comp_of_injective φ e.toMonoidHom e.injective
    rw [this]
    exact hφ2
  have hker2 : IsPGroup 2 ↥(f.comp g).ker := by
    rw [← MonoidHom.comap_ker]
    exact IsPGroup.comap_of_ker_isPGroup hf2 g hg2
  haveI := GoldS146P.sl_simple 3 le_rfl
  have hcard := close16_card_sl_three_two
  refine ⟨f.comp g, ⟨hfs.comp hgs, GoldS146P.sl_simple 3 le_rfl, ?_, ?_, hker2⟩, ?_⟩
  · rintro ⟨⟨h⟩⟩
    obtain ⟨a, b, hab⟩ := GoldS146P.sl_nonabelian 3 le_rfl
    exact hab (h a b)
  · rw [hcard]
    norm_num
  · intro hbot
    have hinj : Function.Injective (f.comp g) := (MonoidHom.ker_eq_bot_iff _).1 hbot
    have hfinj : Function.Injective f := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := hgs x
      obtain ⟨b, rfl⟩ := hgs y
      exact congrArg g (hinj hxy)
    have hf1 : Nat.card ↥f.ker = 1 := by
      rw [(MonoidHom.ker_eq_bot_iff f).2 hfinj]
      exact Subgroup.card_bot
    rw [hf8] at hf1
    exact absurd hf1 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
