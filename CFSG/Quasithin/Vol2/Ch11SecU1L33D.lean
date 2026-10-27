module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

@[expose] def z0c : Code := (13285, false)

@[expose] def tl : List Code :=
  [(2432, false), (2432, true), (2674, false), (2674, true), (4618, false), (4618, true),
   (4862, false), (4862, true), (6643, false), (6643, true), (6725, false), (6725, true),
   (9154, false), (9154, true), (9317, false), (9317, true), (11261, false), (11261, true),
   (11584, false), (11584, true), (13205, false), (13205, true), (13285, false), (13285, true),
   (15634, false), (15634, true), (15959, false), (15959, true), (17903, false), (17903, true),
   (18064, false), (18064, true)]

@[expose] def k0l : List Code :=
  [(828, false), (828, true), (900, false), (900, true), (975, false), (975, true),
   (1221, false), (1221, true), (1548, false), (1548, true), (1638, false), (1638, true),
   (1707, false), (1707, true), (1947, false), (1947, true), (2223, false), (2223, true),
   (2259, false), (2259, true), (2432, false), (2432, true), (2674, false), (2674, true),
   (4419, false), (4419, true), (4437, false), (4437, true), (4618, false), (4618, true),
   (4862, false), (4862, true), (6594, false), (6594, true), (6618, false), (6618, true),
   (6643, false), (6643, true), (6725, false), (6725, true), (13152, false), (13152, true),
   (13182, false), (13182, true), (13205, false), (13205, true), (13285, false), (13285, true)]

@[expose] def q0l : List Code :=
  [(6643, false), (6643, true), (6725, false), (6725, true), (13205, false), (13205, true),
   (13285, false), (13285, true)]

@[expose] def r0l : List Code :=
  [(975, false), (975, true), (1221, false), (1221, true), (1707, false), (1707, true),
   (1947, false), (1947, true), (2223, false), (2223, true), (2259, false), (2259, true),
   (4419, false), (4419, true), (4437, false), (4437, true), (6643, false), (6643, true),
   (6725, false), (6725, true), (13205, false), (13205, true), (13285, false), (13285, true)]

@[expose] def tk0l : List Code :=
  [(2432, false), (2432, true), (2674, false), (2674, true), (4618, false), (4618, true),
   (4862, false), (4862, true), (6643, false), (6643, true), (6725, false), (6725, true),
   (13205, false), (13205, true), (13285, false), (13285, true)]
@[expose] def tableA : List (Code × Code × Code × Code × Code) :=
  [((2432, false), (4862, false), (6643, false), (2432, false), (4862, false)),
   ((2432, false), (13285, false), (6643, false), (2432, false), (13285, false)),
   ((4862, false), (2432, false), (6643, false), (4862, false), (2432, false)),
   ((4862, false), (13285, false), (6643, false), (4862, false), (13285, false)),
   ((6725, false), (13205, false), (9154, false), (2432, false), (4862, false)),
   ((6725, false), (13285, false), (9154, false), (2432, false), (13285, false)),
   ((13205, false), (6725, false), (9154, false), (4862, false), (2432, false)),
   ((13205, false), (13285, false), (9154, false), (4862, false), (13285, false)),
   ((13285, false), (2432, false), (6643, false), (13285, false), (2432, false)),
   ((13285, false), (4862, false), (6643, false), (13285, false), (4862, false)),
   ((13285, false), (6725, false), (9154, false), (13285, false), (2432, false)),
   ((13285, false), (13205, false), (9154, false), (13285, false), (4862, false))]
@[expose] def tableB : List (Code × Code × Code × Code × Code × Code) :=
  [((2432, false), (2432, true), (6643, false), (2432, false), (2432, true), (6643, true)),
   ((2432, false), (4862, true), (6643, false), (2432, false), (4862, true), (13285, true)),
   ((2432, false), (6643, true), (6643, false), (2432, false), (6643, true), (2432, true)),
   ((2432, false), (13285, true), (6643, false), (2432, false), (13285, true), (4862, true)),
   ((4862, false), (2432, true), (6643, false), (4862, false), (2432, true), (13285, true)),
   ((4862, false), (4862, true), (6643, false), (4862, false), (4862, true), (6643, true)),
   ((4862, false), (6643, true), (6643, false), (4862, false), (6643, true), (4862, true)),
   ((4862, false), (13285, true), (6643, false), (4862, false), (13285, true), (2432, true)),
   ((6725, false), (6643, true), (9154, false), (2432, false), (13285, true), (4862, true)),
   ((6725, false), (6725, true), (9154, false), (2432, false), (4862, true), (13285, true)),
   ((6725, false), (13205, true), (9154, false), (2432, false), (2432, true), (6643, true)),
   ((6725, false), (13285, true), (9154, false), (2432, false), (6643, true), (2432, true)),
   ((13205, false), (6643, true), (9154, false), (4862, false), (13285, true), (2432, true)),
   ((13205, false), (6725, true), (9154, false), (4862, false), (4862, true), (6643, true)),
   ((13205, false), (13205, true), (9154, false), (4862, false), (2432, true), (13285, true)),
   ((13205, false), (13285, true), (9154, false), (4862, false), (6643, true), (4862, true)),
   ((13285, false), (2432, true), (6643, false), (13285, false), (2432, true), (4862, true)),
   ((13285, false), (4862, true), (6643, false), (13285, false), (4862, true), (2432, true)),
   ((13285, false), (6643, true), (3060, false), (4862, false), (13285, true), (2432, true)),
   ((13285, false), (6725, true), (9154, false), (13285, false), (4862, true), (2432, true)),
   ((13285, false), (9154, true), (3063, false), (4862, false), (2432, true), (13285, true)),
   ((13285, false), (11584, true), (3066, false), (4862, false), (2432, true), (13285, true)),
   ((13285, false), (13205, true), (9154, false), (13285, false), (2432, true), (4862, true)),
   ((13285, false), (13285, true), (3060, false), (4862, false), (2432, true), (13285, true)),
   ((13285, false), (15634, true), (3066, false), (4862, false), (13285, true), (2432, true)),
   ((13285, false), (18064, true), (3063, false), (4862, false), (13285, true), (2432, true))]
@[expose] def commData : List (Code × Code × Code × Code) :=
  [((2432, false), (975, false), (2223, false), (2432, false)),
   ((2432, true), (975, false), (2223, false), (2432, true)),
   ((2674, false), (975, false), (2223, false), (4618, false)),
   ((2674, true), (975, false), (2223, false), (4618, true)),
   ((4618, false), (975, false), (2223, false), (2674, false)),
   ((4618, true), (975, false), (2223, false), (2674, true)),
   ((4862, false), (975, false), (2223, false), (4862, false)),
   ((4862, true), (975, false), (2223, false), (4862, true))]
@[expose] def pcoreData : List (Code × Code × Code) :=
  [((2432, false), (828, false), (13182, false)), ((2432, true), (828, false), (13182, true)),
   ((2674, false), (828, false), (6594, false)), ((2674, true), (828, false), (6594, true)),
   ((4618, false), (828, false), (6618, false)), ((4618, true), (828, false), (6618, true)),
   ((4862, false), (828, false), (13152, false)), ((4862, true), (828, false), (13152, true))]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
