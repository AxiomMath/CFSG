module

public import CFSG.Quasithin.MS93.MResDefs
public import CFSG.Quasithin.MS93.S46I464
public import CFSG.Quasithin.MS93.S46I467T
public import CFSG.Quasithin.MS93.S46KCT
public import CFSG.Quasithin.MS93.S46R466
public import CFSG.Quasithin.MS93.S46R468Q2

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46R

theorem s468Cfg_of_two (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h467 : I467) {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hq : Fintype.card F = 2) : S468Cfg M T L φ := by
  intro c α β hα hαβ g hg hgN hgZ hodd x hx v hv
  have key : S468At (puAmalgam c.pu.le) α β := by
    by_contra hne
    obtain ⟨α', hc, hg1, hbad⟩ := exists_crit_of_not_s468At h43 h467 c hα hαβ hne
    exact false_of_two h463 h464 h465 h466a c hc (by rw [hg1]; exact hbad) hq
  exact key g ⟨hg, hgN, hgZ, hodd⟩ x hx v hv

@[expose] def S46Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 → IsSL3Full M T L → NotSL3Big L →
      MS93Case11 (Vq M L) T L

theorem s46Two_of (h32 : S32) (h39 : S39) (h42 : S42) (h43 : S43) (h14 : MS14AS)
    (hSQ : SQTKQuot) : S46Two := by
  intro G _ _ M T L h hmin hb4 hfull hL
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hq := card_eq_two_of_via h hL hφ
  have h461 := i461_of h32 h39 h43 h14 hSQ
  have h462 := i462_of h39 h461 h14 hSQ
  have h463 := i463_of h32 h39 h462
  have h464 := i464_of h42 h461 h462 h463 h14 hSQ
  have h465 := i465_of h43 h462 h463 h464
  have h466a := i466a_of (s466aQ4_of_orbit h14 hSQ h43 h462 h463 h464 h465) h464 h465
  have h466b := i466b_of h43 h461 h462 h463 h464 h465 h466a
  have h467 := i467_of_transv h461 h463 h464 h465 h466a
  have h468 : S468Cfg M T L φ := s468Cfg_of_two h43 h463 h464 h465 h466a h467 hq
  have h469 := i469Cfg_of_s468Cfg h43 h463 h464 h465 h466a h466b h467 h468
  have hKC2 := kc4612TwoCfg_of_i469Cfg h463 h464 h465 h466b h467 h469
  have hidx := idx4612Cfg_of_kc2 hKC2 h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have hkc := kc4612Cfg_of_kc2 hKC2 h43 h463 h464 h465 h466a h466b h467 h469
  have h4612 := i4612Cfg_of hkc hidx h14 hSQ h43 h463 h464 h465 h466a h466b h467 h469
  have h46t := i46tCfg_of h14 hSQ h463 h464 h465 h466a h466b h467 h469 h4612
  exact case11_of_i46sCfg h465 h466a h hmin hb4 hφ
    (i46sCfg_of_i46tCfg h14 hSQ h463 h465 h466b h467 h46t)

end CFSG.Quasithin.MS93.MRes
